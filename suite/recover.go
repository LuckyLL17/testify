package suite

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"reflect"
	"regexp"
	"runtime"
	"runtime/debug"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

// Recoverable test run sessions are an opt-in capability. The classic Run
// entry point, test discovery, lifecycle ordering and testing.T behaviour are
// unchanged unless a RunSession is explicitly created.
//
// The capability works in three steps:
//
//  1. BuildPlan derives an immutable TestPlan from a suite value: test methods,
//     the selection expression, execution order, fixture scopes and declared
//     dependencies are captured and fingerprinted.
//  2. NewRunSession + RunSession.Run executes that exact plan. Before anything
//     runs, the current suite is re-fingerprinted; a changed method set,
//     selection or dependency graph aborts execution with ErrPlanMismatch.
//  3. After a failed initial run, RunSession.Rerun replays only the named tests
//     against the same plan with fresh per-test state. Every attempt (original
//     failure and each rerun) stays linked through the plan id, test name and
//     attempt ordinal in the session result.
//
// Lifecycle semantics for a planned execution:
//
//   - SetupSuite runs at most once per session, before the first test. If it
//     panics or fails, no test and no TearDownSuite run. If it skips, the
//     session is skipped and TearDownSuite does not run.
//   - For every started test, SetupTest, BeforeTest, AfterTest and
//     TearDownTest each run exactly once. A failure or panic in SetupTest or
//     BeforeTest suppresses the test body but not AfterTest/TearDownTest.
//     A failure or panic in AfterTest still runs TearDownTest.
//   - A test that is skipped, fails, panics, times out or is canceled keeps
//     the same per-test fixture guarantees; the cleanup hooks run once.
//   - A test that is never started (cancelation of the run, unmet dependency)
//     runs no per-test fixture at all.
//   - TearDownSuite runs at most once per session, when the session is closed.
//   - A rerun repeats no suite-scoped fixture; every rerun attempt gets fresh
//     test-scoped fixtures. A new session resumed from a ResultStore runs the
//     suite-scoped fixtures again for that session.
//
// Go cannot forcibly terminate a goroutine, so timeout and cancelation are
// cooperative: suites that implement TestContextReceiver get a per-test
// context and must observe its cancellation for prompt interruption.

// HookStage identifies one of the suite lifecycle hooks.
type HookStage string

// Lifecycle hook identifiers used in plans, attempts and LifecycleError.
const (
	StageSetupSuite    HookStage = "SetupSuite"
	StageSetupTest     HookStage = "SetupTest"
	StageBeforeTest    HookStage = "BeforeTest"
	StageTest          HookStage = "Test"
	StageAfterTest     HookStage = "AfterTest"
	StageTearDownTest  HookStage = "TearDownTest"
	StageTearDownSuite HookStage = "TearDownSuite"
	StageSignature     HookStage = "signature"
	StageDependency    HookStage = "dependency"
)

// FixtureScope describes whether a fixture is bound to the whole session or
// to a single test attempt.
type FixtureScope string

// Fixture scopes recorded in a plan.
const (
	ScopeSuite FixtureScope = "suite"
	ScopeTest  FixtureScope = "test"
)

// AttemptStatus is the outcome of a single test attempt.
type AttemptStatus string

// Attempt statuses recorded for each test execution.
const (
	StatusPassed   AttemptStatus = "passed"
	StatusFailed   AttemptStatus = "failed"
	StatusSkipped  AttemptStatus = "skipped"
	StatusPanicked AttemptStatus = "panicked"
	StatusTimeout  AttemptStatus = "timeout"
	StatusCanceled AttemptStatus = "canceled"
)

// Sentinel errors. Use errors.Is to distinguish failure classes.
var (
	// ErrInvalidPlan is returned when a plan cannot be built or the rerun
	// request itself is malformed.
	ErrInvalidPlan = errors.New("testify/suite: invalid test plan")
	// ErrPlanMismatch is returned when the suite method set, selection or
	// dependency graph observed at execution time differs from the plan.
	ErrPlanMismatch = errors.New("testify/suite: plan does not match current suite")
	// ErrPlanAlreadyRun is returned when an already consumed plan is submitted
	// for a full run again. No fixture or test is executed in that case.
	ErrPlanAlreadyRun = errors.New("testify/suite: plan has already been consumed")
	// ErrSessionClosed is returned when a closed session is used.
	ErrSessionClosed = errors.New("testify/suite: session is closed")
	// ErrRerunTarget is returned when a rerun names a test that is absent from
	// the plan or whose latest attempt is not a failure.
	ErrRerunTarget = errors.New("testify/suite: invalid rerun target")
	// ErrRerunInProgress is returned by Rerun before the initial run completed.
	ErrRerunInProgress = errors.New("testify/suite: rerun requires a completed initial run")
	// ErrFixtureInit is returned when SetupSuite, SetupTest or BeforeTest
	// fails or panics.
	ErrFixtureInit = errors.New("testify/suite: fixture initialization failed")
	// ErrFixtureCleanup is returned when AfterTest, TearDownTest or
	// TearDownSuite fails or panics.
	ErrFixtureCleanup = errors.New("testify/suite: fixture cleanup failed")
	// ErrConcurrentRun is returned when Run or Rerun is entered while another
	// execution on the same session is still running.
	ErrConcurrentRun = errors.New("testify/suite: concurrent plan execution")
	// ErrTestTimeout is returned when a test exceeds its configured timeout.
	ErrTestTimeout = errors.New("testify/suite: test timed out")
	// ErrRunCanceled is returned when a run is stopped through its context.
	ErrRunCanceled = errors.New("testify/suite: run was canceled")
	// ErrCorruptedResult is returned when persisted session state fails its
	// integrity checks.
	ErrCorruptedResult = errors.New("testify/suite: result record is corrupted")
)

// PlannedFixture describes one lifecycle hook captured by a plan.
type PlannedFixture struct {
	Stage HookStage
	Scope FixtureScope
}

// PlannedTest is one immutable entry of a TestPlan.
type PlannedTest struct {
	name             string
	index            int
	dependsOn        []string
	fixtures         []PlannedFixture
	invalidSignature string
}

// Name is the test method name.
func (p *PlannedTest) Name() string { return p.name }

// Index is the zero-based execution position in the plan.
func (p *PlannedTest) Index() int { return p.index }

// DependsOn returns the declared prerequisite test names, in declaration
// order.
func (p *PlannedTest) DependsOn() []string { return append([]string(nil), p.dependsOn...) }

// Fixtures returns the test-scoped lifecycle hooks that will run for this
// test.
func (p *PlannedTest) Fixtures() []PlannedFixture {
	return append([]PlannedFixture(nil), p.fixtures...)
}

// InvalidSignature is non-empty when the planned method has an invalid test
// signature. The test body reports the returned message instead of invoking
// the method, mirroring the classic runner.
func (p *PlannedTest) InvalidSignature() string { return p.invalidSignature }

// TestPlan is the immutable, fingerprinted description of one suite
// execution.
type TestPlan struct {
	id        string
	suiteType string
	suiteName string
	filter    string
	tests     []*PlannedTest
	byName    map[string]*PlannedTest
	fixtures  []PlannedFixture
	createdAt time.Time
}

// ID is the content fingerprint of the plan. The same suite configuration
// produces the same ID; any change produces another ID.
func (p *TestPlan) ID() string { return p.id }

// SuiteType is "package/path.TypeName" of the planned suite.
func (p *TestPlan) SuiteType() string { return p.suiteType }

// SuiteName is the unqualified suite type name passed to BeforeTest/AfterTest.
func (p *TestPlan) SuiteName() string { return p.suiteName }

// Filter is the frozen regular expression used to select test methods.
func (p *TestPlan) Filter() string { return p.filter }

// Fixtures returns all captured fixtures in scope order.
func (p *TestPlan) Fixtures() []PlannedFixture { return append([]PlannedFixture(nil), p.fixtures...) }

// CreatedAt reports when the plan was built.
func (p *TestPlan) CreatedAt() time.Time { return p.createdAt }

// Tests returns the planned tests in execution order.
func (p *TestPlan) Tests() []*PlannedTest { return append([]*PlannedTest(nil), p.tests...) }

// Test returns the planned test with the given name.
func (p *TestPlan) Test(name string) (*PlannedTest, bool) {
	t, ok := p.byName[name]
	return t, ok
}

type planConfig struct {
	filter string
	deps   map[string][]string
}

// PlanOption configures BuildPlan.
type PlanOption func(*planConfig)

// WithFilter sets the regular expression selecting test methods, mirroring
// the -testify.m flag. The compiled expression is frozen in the plan.
func WithFilter(pattern string) PlanOption {
	return func(c *planConfig) { c.filter = pattern }
}

// WithDependencies declares prerequisite test names. Every dependency must
// name a planned test and the graph must be acyclic. Execution order is
// adjusted so prerequisites run first; a test whose prerequisite did not pass
// in the same run is skipped without running any fixture.
func WithDependencies(deps map[string][]string) PlanOption {
	return func(c *planConfig) {
		c.deps = make(map[string][]string, len(deps))
		for k, v := range deps {
			c.deps[k] = append([]string(nil), v...)
		}
	}
}

type runConfig struct {
	timeout time.Duration
	ctx     context.Context
	store   ResultStore
}

// RunOption configures a RunSession.
type RunOption func(*runConfig)

// WithTestTimeout bounds each test attempt. Suites must cooperate through the
// TestContextReceiver context for prompt interruption; a timeout produces
// ErrTestTimeout and aborts the remaining tests.
func WithTestTimeout(d time.Duration) RunOption {
	return func(c *runConfig) { c.timeout = d }
}

// WithContext attaches a parent context. Canceling it cancels the in-flight
// test and stops further scheduling, returning ErrRunCanceled.
func WithContext(ctx context.Context) RunOption {
	return func(c *runConfig) { c.ctx = ctx }
}

// WithStore selects the result record backing the session. The default is an
// in-memory store; a shared store allows another session to resume the plan
// and rerun failures.
func WithStore(store ResultStore) RunOption {
	return func(c *runConfig) { c.store = store }
}

// TestContextReceiver is implemented by suites that want to observe the
// per-test cancellation context used by WithTestTimeout and WithContext.
// SetTestContext is called with a fresh context before every test attempt,
// including reruns.
type TestContextReceiver interface {
	SetTestContext(ctx context.Context)
}

// BuildPlan derives an immutable plan from the suite value.
func BuildPlan(s TestingSuite, opts ...PlanOption) (*TestPlan, error) {
	if s == nil || reflect.ValueOf(s).IsNil() {
		return nil, fmt.Errorf("%w: nil suite", ErrInvalidPlan)
	}
	cfg := planConfig{filter: *matchMethod}
	for _, opt := range opts {
		opt(&cfg)
	}
	if cfg.filter != "" {
		if _, err := regexp.Compile(cfg.filter); err != nil {
			return nil, fmt.Errorf("%w: invalid filter %q: %v", ErrInvalidPlan, cfg.filter, err)
		}
	}
	plan, err := discoverPlan(s, cfg.filter, cfg.deps)
	if err != nil {
		return nil, err
	}
	return plan, nil
}

type discoveredMethod struct {
	name    string
	numIn   int
	numOut  int
	invalid string
}

func discoverPlan(s TestingSuite, filter string, deps map[string][]string) (*TestPlan, error) {
	methodFinder := reflect.TypeOf(s)
	suiteName := methodFinder.Elem().Name()

	var filterRE *regexp.Regexp
	if filter != "" {
		re, err := regexp.Compile(filter)
		if err != nil {
			return nil, fmt.Errorf("%w: invalid filter %q: %v", ErrInvalidPlan, filter, err)
		}
		filterRE = re
	}

	fixtures := discoverFixtures(s)
	testFixtures := testScopedFixtures(fixtures)

	var methods []discoveredMethod
	for i := 0; i < methodFinder.NumMethod(); i++ {
		method := methodFinder.Method(i)
		if !strings.HasPrefix(method.Name, "Test") {
			continue
		}
		if filterRE != nil && !filterRE.MatchString(method.Name) {
			continue
		}
		dm := discoveredMethod{
			name:   method.Name,
			numIn:  method.Type.NumIn() - 1,
			numOut: method.Type.NumOut(),
		}
		if method.Type.NumIn() > 1 || method.Type.NumOut() > 0 {
			dm.invalid = fmt.Sprintf(
				"testify: suite method %q has invalid signature: expected no input or output parameters, method has %d input parameters and %d output parameters",
				method.Name, dm.numIn, dm.numOut)
		}
		methods = append(methods, dm)
	}
	if len(methods) == 0 {
		return nil, fmt.Errorf("%w: no test methods matched the selection", ErrInvalidPlan)
	}

	byName := make(map[string]*discoveredMethod, len(methods))
	for i := range methods {
		byName[methods[i].name] = &methods[i]
	}
	for name, prereqs := range deps {
		m, ok := byName[name]
		if !ok {
			return nil, fmt.Errorf("%w: dependencies for unknown test %q", ErrInvalidPlan, name)
		}
		if m.invalid != "" {
			return nil, fmt.Errorf("%w: test %q has an invalid signature and cannot declare dependencies", ErrInvalidPlan, name)
		}
		for _, dep := range prereqs {
			d, ok := byName[dep]
			if !ok {
				return nil, fmt.Errorf("%w: test %q depends on unknown test %q", ErrInvalidPlan, name, dep)
			}
			if d.invalid != "" {
				return nil, fmt.Errorf("%w: test %q depends on invalid-signature test %q", ErrInvalidPlan, name, dep)
			}
		}
	}
	if cycle := findDependencyCycle(methods, deps); cycle != nil {
		return nil, fmt.Errorf("%w: dependency cycle: %s", ErrInvalidPlan, strings.Join(cycle, " -> "))
	}

	order := dependencyOrder(methods, deps)
	tests := make([]*PlannedTest, 0, len(order))
	planByName := make(map[string]*PlannedTest, len(order))
	for i, idx := range order {
		m := methods[idx]
		pt := &PlannedTest{
			name:             m.name,
			index:            i,
			dependsOn:        append([]string(nil), deps[m.name]...),
			fixtures:         testFixtures,
			invalidSignature: m.invalid,
		}
		sort.Strings(pt.dependsOn)
		tests = append(tests, pt)
		planByName[pt.name] = pt
	}

	plan := &TestPlan{
		suiteType: methodFinder.Elem().PkgPath() + "." + suiteName,
		suiteName: suiteName,
		filter:    filter,
		tests:     tests,
		byName:    planByName,
		fixtures:  fixtures,
		createdAt: time.Now(),
	}
	plan.id = fingerprint(plan, methods, deps)
	return plan, nil
}

func discoverFixtures(s TestingSuite) []PlannedFixture {
	var f []PlannedFixture
	if _, ok := s.(SetupAllSuite); ok {
		f = append(f, PlannedFixture{Stage: StageSetupSuite, Scope: ScopeSuite})
	}
	if _, ok := s.(TearDownAllSuite); ok {
		f = append(f, PlannedFixture{Stage: StageTearDownSuite, Scope: ScopeSuite})
	}
	if _, ok := s.(SetupTestSuite); ok {
		f = append(f, PlannedFixture{Stage: StageSetupTest, Scope: ScopeTest})
	}
	if _, ok := s.(BeforeTest); ok {
		f = append(f, PlannedFixture{Stage: StageBeforeTest, Scope: ScopeTest})
	}
	if _, ok := s.(AfterTest); ok {
		f = append(f, PlannedFixture{Stage: StageAfterTest, Scope: ScopeTest})
	}
	if _, ok := s.(TearDownTestSuite); ok {
		f = append(f, PlannedFixture{Stage: StageTearDownTest, Scope: ScopeTest})
	}
	if _, ok := s.(SetupSubTest); ok {
		f = append(f, PlannedFixture{Stage: "SetupSubTest", Scope: ScopeTest})
	}
	if _, ok := s.(TearDownSubTest); ok {
		f = append(f, PlannedFixture{Stage: "TearDownSubTest", Scope: ScopeTest})
	}
	return f
}

func testScopedFixtures(all []PlannedFixture) []PlannedFixture {
	var out []PlannedFixture
	for _, f := range all {
		if f.Scope == ScopeTest {
			out = append(out, f)
		}
	}
	return out
}

func findDependencyCycle(methods []discoveredMethod, deps map[string][]string) []string {
	white := map[string]bool{}
	for _, m := range methods {
		white[m.name] = true
	}
	var stack []string
	var visit func(name string) []string
	visit = func(name string) []string {
		if !white[name] {
			for _, n := range stack {
				if n == name {
					return append(append([]string(nil), stack...), name)
				}
			}
			return nil
		}
		delete(white, name)
		stack = append(stack, name)
		prereqs := append([]string(nil), deps[name]...)
		sort.Strings(prereqs)
		for _, dep := range prereqs {
			if cyc := visit(dep); cyc != nil {
				return cyc
			}
		}
		stack = stack[:len(stack)-1]
		return nil
	}
	names := make([]string, 0, len(methods))
	for _, m := range methods {
		names = append(names, m.name)
	}
	sort.Strings(names)
	for _, n := range names {
		if cyc := visit(n); cyc != nil {
			return cyc
		}
	}
	return nil
}

// dependencyOrder returns indices into methods in an order satisfying deps
// (stable: discovery/lexicographic order is preserved whenever possible).
func dependencyOrder(methods []discoveredMethod, deps map[string][]string) []int {
	indexByName := make(map[string]int, len(methods))
	for i, m := range methods {
		indexByName[m.name] = i
	}
	indegree := make(map[string]int, len(methods))
	dependents := make(map[string][]string, len(methods))
	for name, prereqs := range deps {
		indegree[name] = len(prereqs)
		for _, dep := range prereqs {
			dependents[dep] = append(dependents[dep], name)
		}
	}
	var ready []int
	for i, m := range methods {
		if indegree[m.name] == 0 {
			ready = append(ready, i)
		}
	}
	var order []int
	for len(ready) > 0 {
		idx := ready[0]
		ready = ready[1:]
		order = append(order, idx)
		for _, dep := range dependents[methods[idx].name] {
			indegree[dep]--
			if indegree[dep] == 0 {
				ready = append(ready, indexByName[dep])
				sort.Ints(ready)
			}
		}
	}
	return order
}

func fingerprint(plan *TestPlan, methods []discoveredMethod, deps map[string][]string) string {
	h := sha256.New()
	fmt.Fprintf(h, "testify-suite-recoverable/v1\nsuite=%s\nfilter=%q\n", plan.suiteType, plan.filter)
	for _, f := range plan.fixtures {
		fmt.Fprintf(h, "fixture=%s:%s\n", f.Scope, f.Stage)
	}
	for _, m := range methods {
		fmt.Fprintf(h, "method=%s:in=%d,out=%d\n", m.name, m.numIn, m.numOut)
	}
	names := make([]string, 0, len(deps))
	for name := range deps {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		prereqs := append([]string(nil), deps[name]...)
		sort.Strings(prereqs)
		fmt.Fprintf(h, "deps=%s=%s\n", name, strings.Join(prereqs, ","))
	}
	return hex.EncodeToString(h.Sum(nil))
}

// verifyPlan re-derives the fingerprint from the current suite value and the
// frozen plan configuration.
func verifyPlan(plan *TestPlan, s TestingSuite) error {
	deps := make(map[string][]string, len(plan.tests))
	for _, pt := range plan.tests {
		if len(pt.dependsOn) > 0 {
			deps[pt.name] = pt.DependsOn()
		}
	}
	current, err := discoverPlan(s, plan.filter, deps)
	if err != nil {
		return &PlanMismatchError{Reason: "suite cannot be re-discovered: " + err.Error()}
	}
	if current.suiteType != plan.suiteType {
		return &PlanMismatchError{Reason: fmt.Sprintf("suite type changed: %q != %q", current.suiteType, plan.suiteType)}
	}
	if current.id != plan.id {
		switch {
		case len(current.tests) != len(plan.tests):
			return &PlanMismatchError{Reason: fmt.Sprintf("test method set changed: plan has %d tests, suite now has %d", len(plan.tests), len(current.tests))}
		case !fixturesEqual(current.fixtures, plan.fixtures):
			return &PlanMismatchError{Reason: "fixture (lifecycle hook) set changed"}
		default:
			for i := range plan.tests {
				a := plan.tests[i]
				b := current.tests[i]
				if a.name != b.name || a.invalidSignature != b.invalidSignature || !equalStrings(a.dependsOn, b.dependsOn) {
					return &PlanMismatchError{Reason: fmt.Sprintf("test %q changed (name, signature or dependencies)", a.name)}
				}
			}
			return &PlanMismatchError{Reason: "selection or method signatures changed"}
		}
	}
	return nil
}

func fixturesEqual(a, b []PlannedFixture) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func equalStrings(a, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// PlanMismatchError wraps ErrPlanMismatch with a concrete reason.
type PlanMismatchError struct {
	Reason string
}

func (e *PlanMismatchError) Error() string { return e.Reason }
func (e *PlanMismatchError) Unwrap() error { return ErrPlanMismatch }

// LifecycleError wraps ErrFixtureInit or ErrFixtureCleanup and identifies the
// hook and (for test-scoped hooks) the test.
type LifecycleError struct {
	Stage     HookStage
	TestName  string
	Recovered interface{}
	Message   string
}

func (e *LifecycleError) Error() string {
	scope := string(e.Stage)
	if e.TestName != "" {
		scope += "/" + e.TestName
	}
	if e.Message != "" {
		return fmt.Sprintf("testify/suite: fixture failure in %s: %s", scope, e.Message)
	}
	return fmt.Sprintf("testify/suite: fixture failure in %s", scope)
}

func (e *LifecycleError) Unwrap() error {
	switch e.Stage {
	case StageAfterTest, StageTearDownTest, StageTearDownSuite:
		return ErrFixtureCleanup
	default:
		return ErrFixtureInit
	}
}

// TimeoutError wraps ErrTestTimeout.
type TimeoutError struct {
	TestName string
	Timeout  time.Duration
}

func (e *TimeoutError) Error() string {
	return fmt.Sprintf("testify/suite: test %q did not finish within %s", e.TestName, e.Timeout)
}
func (e *TimeoutError) Unwrap() error { return ErrTestTimeout }

// RunCanceledError wraps ErrRunCanceled.
type RunCanceledError struct {
	Reason string
}

func (e *RunCanceledError) Error() string {
	if e.Reason != "" {
		return "testify/suite: run was canceled: " + e.Reason
	}
	return "testify/suite: run was canceled"
}
func (e *RunCanceledError) Unwrap() error { return ErrRunCanceled }

// RerunTargetError wraps ErrRerunTarget.
type RerunTargetError struct {
	TestName string
	Reason   string
}

func (e *RerunTargetError) Error() string {
	return fmt.Sprintf("testify/suite: cannot rerun %q: %s", e.TestName, e.Reason)
}
func (e *RerunTargetError) Unwrap() error { return ErrRerunTarget }

// CorruptionError wraps ErrCorruptedResult.
type CorruptionError struct {
	Detail string
}

func (e *CorruptionError) Error() string {
	return "testify/suite: result record is corrupted: " + e.Detail
}
func (e *CorruptionError) Unwrap() error { return ErrCorruptedResult }

type multiError struct {
	errs []error
}

func (m *multiError) add(err error) {
	if err != nil {
		m.errs = append(m.errs, err)
	}
}
func (m *multiError) err() error {
	if len(m.errs) == 0 {
		return nil
	}
	if len(m.errs) == 1 {
		return m.errs[0]
	}
	return m
}
func (m *multiError) Error() string {
	parts := make([]string, len(m.errs))
	for i, e := range m.errs {
		parts[i] = e.Error()
	}
	return strings.Join(parts, "; ")
}
func (m *multiError) Is(target error) bool {
	for _, e := range m.errs {
		if errors.Is(e, target) {
			return true
		}
	}
	return false
}
func (m *multiError) As(target interface{}) bool {
	for _, e := range m.errs {
		if errors.As(e, target) {
			return true
		}
	}
	return false
}

// RunSession executes an immutable TestPlan and supports reruns of failed
// tests against the same plan.
type RunSession struct {
	t       *testing.T
	plan    *TestPlan
	suite   TestingSuite
	store   ResultStore
	timeout time.Duration
	rootCtx context.Context
	cancel  context.CancelFunc

	gate int32 // non-blocking run lock: 0 idle, 1 executing

	mu           sync.Mutex
	closed       bool
	consumed     bool
	suiteReady   bool // SetupSuite completed successfully
	suiteSkipped bool
	poisoned     error // first non-recoverable store failure, if any
	state        *storedState
}

func runtimeGoexit() { runtime.Goexit() }

// NewRunSession binds a plan to a suite value and a result store. The plan is
// verified against the suite before the session is returned. The session
// registers a testing cleanup that closes it, so TearDownSuite always runs
// exactly once.
func NewRunSession(t *testing.T, plan *TestPlan, s TestingSuite, opts ...RunOption) (*RunSession, error) {
	if plan == nil {
		return nil, fmt.Errorf("%w: nil plan", ErrInvalidPlan)
	}
	if s == nil || reflect.ValueOf(s).IsNil() {
		return nil, fmt.Errorf("%w: nil suite", ErrInvalidPlan)
	}
	cfg := runConfig{ctx: context.Background(), store: NewMemoryStore()}
	for _, opt := range opts {
		opt(&cfg)
	}
	if cfg.timeout < 0 {
		return nil, fmt.Errorf("%w: negative timeout", ErrInvalidPlan)
	}
	if cfg.ctx == nil {
		return nil, fmt.Errorf("%w: nil context", ErrInvalidPlan)
	}
	if err := verifyPlan(plan, s); err != nil {
		return nil, err
	}

	state, found, err := cfg.store.Load(plan.id)
	if err != nil {
		return nil, err
	}
	if found {
		if err := validateState(state); err != nil {
			return nil, err
		}
		if err := crossCheckState(plan, state); err != nil {
			return nil, err
		}
	} else {
		state = &storedState{Version: 1, PlanID: plan.id, Attempts: map[string][]storedAttempt{}}
		if err := cfg.store.Save(plan.id, state); err != nil {
			return nil, err
		}
	}

	rootCtx, cancel := context.WithCancel(cfg.ctx)
	session := &RunSession{
		t:        t,
		plan:     plan,
		suite:    s,
		store:    cfg.store,
		timeout:  cfg.timeout,
		rootCtx:  rootCtx,
		cancel:   cancel,
		consumed: state.Consumed,
		state:    state,
	}
	session.suite.SetT(t)
	session.suite.SetS(session.suite)
	t.Cleanup(func() {
		if err := session.Close(); err != nil && !errors.Is(err, ErrSessionClosed) {
			t.Errorf("%v", err)
		}
	})
	return session, nil
}

// Plan returns the immutable plan of the session.
func (s *RunSession) Plan() *TestPlan { return s.plan }

// Cancel requests cancellation of the current or next run. It is safe to call
// concurrently.
func (s *RunSession) Cancel() { s.cancel() }

func (s *RunSession) acquireGate() error {
	if !atomic.CompareAndSwapInt32(&s.gate, 0, 1) {
		return ErrConcurrentRun
	}
	return nil
}

func (s *RunSession) releaseGate() { atomic.StoreInt32(&s.gate, 0) }

// Run executes the whole plan once. A second full submission of the same plan
// fails with ErrPlanAlreadyRun without side effects.
func (s *RunSession) Run() (err error) {
	s.mu.Lock()
	if s.closed {
		s.mu.Unlock()
		return ErrSessionClosed
	}
	if s.consumed {
		s.mu.Unlock()
		return ErrPlanAlreadyRun
	}
	if s.poisoned != nil {
		err := s.poisoned
		s.mu.Unlock()
		return err
	}
	s.mu.Unlock()

	if err := s.acquireGate(); err != nil {
		return err
	}
	defer s.releaseGate()

	if err := verifyPlan(s.plan, s.suite); err != nil {
		return err
	}

	return s.execute(runKindInitial, nil)
}

// Rerun executes only the named failed tests against the same plan, in plan
// order, using fresh test-scoped fixtures and state. The request is validated
// completely before any fixture runs, so a bad target set has no side
// effects.
func (s *RunSession) Rerun(testNames ...string) error {
	if len(testNames) == 0 {
		return fmt.Errorf("%w: no test names given", ErrRerunTarget)
	}
	s.mu.Lock()
	if s.closed {
		s.mu.Unlock()
		return ErrSessionClosed
	}
	s.mu.Unlock()

	// Concurrent submission is rejected before any target inspection so a
	// rerun can never interleave with a run or another rerun.
	if err := s.acquireGate(); err != nil {
		return err
	}
	defer s.releaseGate()

	s.mu.Lock()
	if !s.consumed {
		s.mu.Unlock()
		return ErrRerunInProgress
	}
	if s.poisoned != nil {
		err := s.poisoned
		s.mu.Unlock()
		return err
	}
	s.mu.Unlock()

	seen := map[string]bool{}
	targets := make([]*PlannedTest, 0, len(testNames))
	for _, name := range testNames {
		if seen[name] {
			return &RerunTargetError{TestName: name, Reason: "duplicated in the same rerun request"}
		}
		seen[name] = true
		pt, ok := s.plan.Test(name)
		if !ok {
			return &RerunTargetError{TestName: name, Reason: "not part of the plan"}
		}
		latest, ok := s.latestAttempt(name)
		if !ok {
			return &RerunTargetError{TestName: name, Reason: "test never ran"}
		}
		switch latest.Status {
		case StatusFailed, StatusPanicked, StatusTimeout:
		case StatusSkipped:
			// A test skipped because a prerequisite failed may be rerun once
			// the prerequisite is fixed; an explicit t.Skip may not.
			if latest.FailureStage != StageDependency {
				return &RerunTargetError{TestName: name, Reason: "latest attempt is " + string(latest.Status)}
			}
		default:
			return &RerunTargetError{TestName: name, Reason: "latest attempt is " + string(latest.Status)}
		}
		targets = append(targets, pt)
	}
	sort.Slice(targets, func(i, j int) bool { return targets[i].index < targets[j].index })

	if err := verifyPlan(s.plan, s.suite); err != nil {
		return err
	}

	names := make([]string, len(targets))
	for i, pt := range targets {
		names[i] = pt.name
	}
	return s.execute(runKindRerun, names)
}

// Close runs TearDownSuite once when SetupSuite had completed and releases the
// session. Further calls return ErrSessionClosed without side effects.
func (s *RunSession) Close() error {
	s.mu.Lock()
	if s.closed {
		s.mu.Unlock()
		return ErrSessionClosed
	}
	s.closed = true
	ready := s.suiteReady
	s.mu.Unlock()

	s.cancel()

	var errs multiError
	if ready {
		if err := s.runTearDownSuite(); err != nil {
			errs.add(err)
		}
	}
	s.mu.Lock()
	s.suiteReady = false
	s.mu.Unlock()
	if err := s.persist(); err != nil {
		errs.add(err)
	}
	return errs.err()
}

const (
	runKindInitial = "initial"
	runKindRerun   = "rerun"
)

func (s *RunSession) execute(kind string, targets []string) (err error) {
	var errs multiError

	run := storedRun{
		ID:      newRunID(kind),
		Kind:    kind,
		Targets: append([]string(nil), targets...),
		Start:   time.Now(),
	}
	s.mu.Lock()
	s.state.Runs = append(s.state.Runs, run)
	runIndex := len(s.state.Runs) - 1
	s.mu.Unlock()
	if perr := s.persist(); perr != nil {
		s.poison(perr)
		return perr
	}

	defer func() {
		s.mu.Lock()
		s.state.Runs[runIndex].End = time.Now()
		s.mu.Unlock()
		if perr := s.persist(); perr != nil {
			errs.add(perr)
		}
		err = errs.err()
	}()

	if !s.suiteReady && !s.suiteSkipped {
		if lerr := s.runSetupSuite(); lerr != nil {
			errs.add(lerr)
			return
		}
	}

	selected := s.plan.tests
	if kind == runKindRerun {
		wanted := make(map[string]bool, len(targets))
		for _, n := range targets {
			wanted[n] = true
		}
		selected = make([]*PlannedTest, 0, len(targets))
		for _, pt := range s.plan.tests {
			if wanted[pt.name] {
				selected = append(selected, pt)
			}
		}
	}
	isSelected := make(map[string]bool, len(selected))
	for _, pt := range selected {
		isSelected[pt.name] = true
	}

	passedInThisRun := map[string]bool{}
	aborted := false
	var abortReason error
	for _, pt := range s.plan.tests {
		if !isSelected[pt.name] {
			continue
		}
		if aborted {
			s.recordAttempt(run.ID, pt, StatusCanceled, "", "run aborted before test started")
			if perr := s.persistError(); perr != nil {
				aborted = true
				abortReason = perr
				break
			}
			continue
		}
		if err := s.rootCtx.Err(); err != nil {
			s.recordAttempt(run.ID, pt, StatusCanceled, "", "run canceled before test started")
			aborted = true
			if perr := s.persistError(); perr != nil {
				abortReason = perr
			} else {
				abortReason = &RunCanceledError{Reason: err.Error()}
			}
			continue
		}
		if unmet := s.unmetDependency(pt, passedInThisRun); unmet != "" {
			s.recordAttempt(run.ID, pt, StatusSkipped, StageDependency,
				"dependency "+unmet+" did not pass")
			if perr := s.persistError(); perr != nil {
				aborted = true
				abortReason = perr
				break
			}
			continue
		}

		attempt := s.runOneTest(run.ID, pt)
		if perr := s.persistError(); perr != nil {
			aborted = true
			abortReason = perr
			break
		}
		if attempt.Status == StatusPassed {
			passedInThisRun[pt.name] = true
		}
		for _, le := range attempt.lifecycleErrors() {
			errs.add(le)
		}
		switch attempt.Status {
		case StatusTimeout:
			aborted = true
			abortReason = &TimeoutError{TestName: pt.name, Timeout: s.timeout}
		case StatusCanceled:
			aborted = true
			abortReason = &RunCanceledError{Reason: "canceled while running " + pt.name}
		}
	}
	if abortReason != nil {
		errs.add(abortReason)
	}
	s.mu.Lock()
	if !s.suiteSkipped && s.poisoned == nil {
		// SetupSuite succeeded and the run reached scheduling: the plan is
		// consumed regardless of test outcomes or interruption. A poisoned
		// record leaves the durable state unconfirmed, so consumption is not
		// marked and further runs are refused until the store is fixed.
		s.consumed = true
		s.state.Consumed = true
	}
	s.mu.Unlock()
	return errs.err()
}

func (s *RunSession) unmetDependency(pt *PlannedTest, passed map[string]bool) string {
	for _, dep := range pt.dependsOn {
		if passed[dep] {
			continue
		}
		if latest, ok := s.latestAttempt(dep); ok && latest.Status == StatusPassed {
			continue
		}
		return dep
	}
	return ""
}

func (s *RunSession) runSetupSuite() *LifecycleError {
	h, ok := s.suite.(SetupAllSuite)
	if !ok {
		s.mu.Lock()
		s.suiteReady = true
		s.mu.Unlock()
		return nil
	}
	var recovered interface{}
	completed := false
	func() {
		defer func() {
			recovered = recover()
		}()
		h.SetupSuite()
		completed = true
	}()
	if s.t.Skipped() {
		s.mu.Lock()
		s.suiteSkipped = true
		s.mu.Unlock()
		// Skip uses runtime.Goexit inside the isolated closure; re-raise on
		// the test goroutine so the enclosing test is reported as skipped and
		// the run's defers execute.
		runtimeGoexit()
	}
	if recovered != nil {
		s.t.Errorf("test panicked: %v\n%s", recovered, debug.Stack())
		return &LifecycleError{Stage: StageSetupSuite, Recovered: recovered, Message: fmt.Sprint(recovered)}
	}
	if !completed && s.t.Failed() {
		return &LifecycleError{Stage: StageSetupSuite, Message: "test failure reported in SetupSuite"}
	}
	s.mu.Lock()
	s.suiteReady = true
	s.mu.Unlock()
	return nil
}

func (s *RunSession) runTearDownSuite() error {
	h, ok := s.suite.(TearDownAllSuite)
	if !ok {
		return nil
	}
	// A failed subtest already fails the parent T; only failures originating
	// inside TearDownSuite itself are attributed to the fixture.
	failedBefore := s.t.Failed()
	var recovered interface{}
	completed := false
	func() {
		defer func() { recovered = recover() }()
		h.TearDownSuite()
		completed = true
	}()
	if recovered != nil {
		s.t.Errorf("test panicked: %v\n%s", recovered, debug.Stack())
		return &LifecycleError{Stage: StageTearDownSuite, Recovered: recovered, Message: fmt.Sprint(recovered)}
	}
	if !completed && s.t.Failed() && !failedBefore {
		return &LifecycleError{Stage: StageTearDownSuite, Message: "test failure reported in TearDownSuite"}
	}
	return nil
}

// testOutcome carries the finalized attempt out of the worker goroutine.
type testOutcome struct {
	stage      HookStage
	recovered  interface{}
	hookErrors []*LifecycleError
}

func (s *RunSession) runOneTest(runID string, pt *PlannedTest) storedAttempt {
	attemptNo := s.nextAttemptNumber(pt.name)
	attempt := storedAttempt{
		RunID:    runID,
		Attempt:  attemptNo,
		TestName: pt.name,
		Start:    time.Now(),
	}

	s.t.Run(pt.name, func(it *testing.T) {
		if pt.invalidSignature != "" {
			it.Error(pt.invalidSignature)
			attempt.Status = StatusFailed
			attempt.FailureStage = StageSignature
			attempt.Failure = pt.invalidSignature
			return
		}

		attemptCtx, cancelAttempt := context.WithCancel(s.rootCtx)
		if s.timeout > 0 {
			attemptCtx, cancelAttempt = context.WithTimeout(s.rootCtx, s.timeout)
		}
		defer cancelAttempt()
		if rx, ok := s.suite.(TestContextReceiver); ok {
			rx.SetTestContext(attemptCtx)
		}

		outcome := &testOutcome{stage: StageSetupTest}
		done := make(chan struct{})
		go func() {
			defer close(done)
			s.runTestWorker(it, pt, outcome)
		}()
		select {
		case <-done:
		case <-attemptCtx.Done():
			// Timeout or cancel: wait for the cooperative worker to leave.
			<-done
		}

		finalize := func() {
			attempt.End = time.Now()
			switch {
			case attemptCtx.Err() == context.DeadlineExceeded:
				attempt.Status = StatusTimeout
				attempt.FailureStage = StageTest
				attempt.Failure = "test exceeded " + s.timeout.String()
				it.Errorf("test %q timed out after %s", pt.name, s.timeout)
			case attemptCtx.Err() == context.Canceled && s.rootCtx.Err() == context.Canceled:
				attempt.Status = StatusCanceled
				attempt.FailureStage = ""
				attempt.Failure = "run canceled"
			default:
				s.fillBodyStatus(it, &attempt, outcome)
			}
			attempt.hookErrs = outcome.hookErrors
		}
		finalize()
	})

	if attempt.End.IsZero() {
		attempt.End = time.Now()
	}
	s.appendAttempt(attempt)
	return attempt
}

func (s *RunSession) fillBodyStatus(it *testing.T, attempt *storedAttempt, o *testOutcome) {
	switch {
	case it.Skipped():
		attempt.Status = StatusSkipped
	case o.recovered != nil && o.stage == StageTest:
		attempt.Status = StatusPanicked
		attempt.FailureStage = StageTest
		attempt.Failure = fmt.Sprint(o.recovered)
	case o.recovered != nil:
		attempt.Status = StatusFailed
		attempt.FailureStage = o.stage
		attempt.Failure = fmt.Sprint(o.recovered)
	case len(o.hookErrors) > 0:
		attempt.Status = StatusFailed
		last := o.hookErrors[len(o.hookErrors)-1]
		attempt.FailureStage = last.Stage
		attempt.Failure = last.Message
	case it.Failed():
		attempt.Status = StatusFailed
		attempt.FailureStage = o.stage
	default:
		attempt.Status = StatusPassed
	}
}

// runTestWorker executes SetupTest, BeforeTest, the body, AfterTest and
// TearDownTest. It runs in a dedicated goroutine so the outer callback can
// watch the attempt context. The ordering and recovery rules mirror the
// classic suite runner.
func (s *RunSession) runTestWorker(it *testing.T, pt *PlannedTest, o *testOutcome) {
	parentT := s.suite.T()
	s.suite.SetT(it)
	defer func() {
		it.Helper()

		r := recover()
		if r != nil {
			o.recovered = r
			it.Errorf("test panicked: %v\n%s", r, debug.Stack())
		}

		if h, ok := s.suite.(AfterTest); ok {
			if le := s.callIsolatedHook(it, pt.name, StageAfterTest, func() {
				h.AfterTest(s.plan.suiteName, pt.name)
			}); le != nil {
				o.hookErrors = append(o.hookErrors, le)
			}
		}
		if h, ok := s.suite.(TearDownTestSuite); ok {
			if le := s.callIsolatedHook(it, pt.name, StageTearDownTest, h.TearDownTest); le != nil {
				o.hookErrors = append(o.hookErrors, le)
			}
		}

		s.suite.SetT(parentT)

		if r != nil {
			// Mirror failOnPanic: end the (worker) goroutine immediately.
			it.FailNow()
		}
	}()

	if h, ok := s.suite.(SetupTestSuite); ok {
		o.stage = StageSetupTest
		h.SetupTest()
	}
	if h, ok := s.suite.(BeforeTest); ok {
		o.stage = StageBeforeTest
		h.BeforeTest(s.plan.suiteName, pt.name)
	}
	o.stage = StageTest
	method := reflect.ValueOf(s.suite).MethodByName(pt.name)
	method.Call(nil)
}

func (s *RunSession) callIsolatedHook(it *testing.T, testName string, stage HookStage, fn func()) *LifecycleError {
	var recovered interface{}
	normalEnd := false
	func() {
		defer func() { recovered = recover() }()
		fn()
		normalEnd = true
	}()
	if recovered != nil {
		it.Helper()
		it.Errorf("fixture %s panicked: %v\n%s", stage, recovered, debug.Stack())
		return &LifecycleError{Stage: stage, TestName: testName, Recovered: recovered, Message: fmt.Sprint(recovered)}
	}
	if !normalEnd && it.Failed() {
		return &LifecycleError{Stage: stage, TestName: testName, Message: "test failure reported in " + string(stage)}
	}
	return nil
}

func (s *RunSession) nextAttemptNumber(name string) int {
	s.mu.Lock()
	defer s.mu.Unlock()
	return len(s.state.Attempts[name]) + 1
}

func (s *RunSession) recordAttempt(runID string, pt *PlannedTest, status AttemptStatus, stage HookStage, failure string) {
	a := storedAttempt{
		RunID:        runID,
		Attempt:      s.nextAttemptNumber(pt.name),
		TestName:     pt.name,
		Status:       status,
		FailureStage: stage,
		Failure:      failure,
		Start:        time.Now(),
		End:          time.Now(),
	}
	s.appendAttempt(a)
}

func (s *RunSession) appendAttempt(a storedAttempt) {
	s.mu.Lock()
	s.state.Attempts[a.TestName] = append(s.state.Attempts[a.TestName], a)
	s.mu.Unlock()
	if err := s.persist(); err != nil {
		s.poison(err)
	}
}

func (s *RunSession) poison(err error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.poisoned == nil {
		s.poisoned = err
	}
}

func (s *RunSession) persistError() error {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.poisoned
}

func (s *RunSession) latestAttempt(name string) (storedAttempt, bool) {
	s.mu.Lock()
	defer s.mu.Unlock()
	attempts := s.state.Attempts[name]
	if len(attempts) == 0 {
		return storedAttempt{}, false
	}
	return attempts[len(attempts)-1], true
}

func (s *RunSession) persist() error {
	s.mu.Lock()
	snapshot := cloneState(s.state)
	snapshot.Version = s.state.Version + 1
	s.mu.Unlock()
	if err := s.store.Save(s.plan.id, snapshot); err != nil {
		return err
	}
	s.mu.Lock()
	s.state.Version = snapshot.Version
	s.mu.Unlock()
	return nil
}

// TestAttempt is the public view of one test execution.
type TestAttempt struct {
	RunID        string
	Attempt      int
	TestName     string
	Status       AttemptStatus
	FailureStage HookStage
	Failure      string
	Start        time.Time
	End          time.Time
}

// RunResult is the public view of one initial run or one rerun.
type RunResult struct {
	ID      string
	Kind    string
	Targets []string
	Tests   []TestAttempt
}

// SessionResult is the correlated history of all runs of a plan in this
// session, including attempts loaded from the store.
type SessionResult struct {
	PlanID string
	Runs   []*RunResult
}

// Result returns the correlated run history. The returned value is a copy.
func (s *RunSession) Result() *SessionResult {
	s.mu.Lock()
	defer s.mu.Unlock()
	out := &SessionResult{PlanID: s.plan.id, Runs: make([]*RunResult, 0, len(s.state.Runs))}
	for _, r := range s.state.Runs {
		rr := &RunResult{ID: r.ID, Kind: r.Kind, Targets: append([]string(nil), r.Targets...)}
		for _, pt := range s.plan.tests {
			for _, a := range s.state.Attempts[pt.name] {
				if a.RunID == r.ID {
					rr.Tests = append(rr.Tests, publicAttempt(a))
				}
			}
		}
		out.Runs = append(out.Runs, rr)
	}
	return out
}

// Attempts returns every attempt of a test in chronological order, linking
// the original failure with subsequent reruns.
func (r *SessionResult) Attempts(testName string) []TestAttempt {
	var out []TestAttempt
	for _, run := range r.Runs {
		for _, a := range run.Tests {
			if a.TestName == testName {
				out = append(out, a)
			}
		}
	}
	return out
}

// Latest returns the most recent attempt of a test.
func (r *SessionResult) Latest(testName string) (TestAttempt, bool) {
	all := r.Attempts(testName)
	if len(all) == 0 {
		return TestAttempt{}, false
	}
	return all[len(all)-1], true
}

// OriginalFailure returns the first failed, panicked or timed-out attempt of a
// test, i.e. the failure a later rerun is associated with.
func (r *SessionResult) OriginalFailure(testName string) (TestAttempt, bool) {
	for _, a := range r.Attempts(testName) {
		switch a.Status {
		case StatusFailed, StatusPanicked, StatusTimeout:
			return a, true
		}
	}
	return TestAttempt{}, false
}

func publicAttempt(a storedAttempt) TestAttempt {
	return TestAttempt{
		RunID:        a.RunID,
		Attempt:      a.Attempt,
		TestName:     a.TestName,
		Status:       a.Status,
		FailureStage: a.FailureStage,
		Failure:      a.Failure,
		Start:        a.Start,
		End:          a.End,
	}
}

var runSequence uint64

func newRunID(kind string) string {
	seq := atomic.AddUint64(&runSequence, 1)
	return fmt.Sprintf("%s-%d-%d", kind, time.Now().UnixNano(), seq)
}
