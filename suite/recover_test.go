package suite

import (
	"context"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"os"
	"path/filepath"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// runRecoverIsolated executes f as an isolated go test and reports whether it
// succeeded, so planned failures do not poison the enclosing test.
func runRecoverIsolated(t *testing.T, name string, f func(t *testing.T)) bool {
	t.Helper()
	return testing.RunTests(allTestsFilter, []testing.InternalTest{{
		Name: t.Name() + "/" + name,
		F:    f,
	}})
}

// recoverCallRecorder records lifecycle calls in order.
type recoverCallRecorder struct {
	mu    sync.Mutex
	calls []string
}

func (r *recoverCallRecorder) add(call string) {
	r.mu.Lock()
	r.calls = append(r.calls, call)
	r.mu.Unlock()
}

func (r *recoverCallRecorder) snapshot() []string {
	r.mu.Lock()
	defer r.mu.Unlock()
	return append([]string(nil), r.calls...)
}

func (r *recoverCallRecorder) count(call string) int {
	r.mu.Lock()
	defer r.mu.Unlock()
	n := 0
	for _, c := range r.calls {
		if c == call {
			n++
		}
	}
	return n
}

// recSessionSuite is a fully instrumented suite used by the recoverable
// session tests.
type recSessionSuite struct {
	Suite
	rec *recoverCallRecorder

	mu sync.Mutex

	// Per-test behavior toggles.
	errorTests map[string]bool
	fatalTests map[string]bool
	panicTests map[string]bool
	skipTests  map[string]bool
	hangCtx    map[string]bool // cooperate with the test context
	hold       map[string]chan struct{}

	// Hook behavior toggles, keyed by 1-based per-hook invocation.
	panicHookAt map[HookStage]int
	fatalHookAt map[HookStage]int
	panicSetup  bool
	panicTeard  bool

	ctx       context.Context
	testRuns  map[string]int
	setupN    int
	teardownN int
	started   map[string]chan struct{}
}

func newRecSessionSuite(rec *recoverCallRecorder) *recSessionSuite {
	return &recSessionSuite{
		rec:         rec,
		errorTests:  map[string]bool{},
		fatalTests:  map[string]bool{},
		panicTests:  map[string]bool{},
		skipTests:   map[string]bool{},
		hangCtx:     map[string]bool{},
		hold:        map[string]chan struct{}{},
		panicHookAt: map[HookStage]int{},
		fatalHookAt: map[HookStage]int{},
		testRuns:    map[string]int{},
		started:     map[string]chan struct{}{},
	}
}

func (s *recSessionSuite) SetTestContext(ctx context.Context) {
	s.mu.Lock()
	s.ctx = ctx
	s.mu.Unlock()
}

func (s *recSessionSuite) SetupSuite() {
	s.rec.add("SetupSuite")
	if s.panicSetup {
		panic("setup-suite-boom")
	}
}

func (s *recSessionSuite) SetupTest() {
	s.setupN++
	s.rec.add("SetupTest")
	if s.panicHookAt[StageSetupTest] == s.setupN {
		panic("setup-test-boom")
	}
	if s.fatalHookAt[StageSetupTest] == s.setupN {
		s.T().Fatal("setup-test-fatal")
	}
}

func (s *recSessionSuite) BeforeTest(_, name string) {
	s.rec.add("BeforeTest:" + name)
	if s.panicHookAt[StageBeforeTest] == s.testRunOrdinal(name) {
		panic("before-test-boom")
	}
}

func (s *recSessionSuite) AfterTest(_, name string) {
	s.rec.add("AfterTest:" + name)
	if s.panicHookAt[StageAfterTest] == s.testRunOrdinal(name) {
		panic("after-test-boom")
	}
}

func (s *recSessionSuite) TearDownTest() {
	s.teardownN++
	s.rec.add("TearDownTest")
	if s.panicHookAt[StageTearDownTest] == s.teardownN {
		panic("teardown-test-boom")
	}
}

func (s *recSessionSuite) TearDownSuite() {
	s.rec.add("TearDownSuite")
	if s.panicTeard {
		panic("teardown-suite-boom")
	}
}

// testRunOrdinal returns the 1-based ordinal of the test in plan order.
func (s *recSessionSuite) testRunOrdinal(name string) int {
	switch name {
	case "TestAlpha":
		return 1
	case "TestBeta":
		return 2
	default:
		return 3
	}
}

func (s *recSessionSuite) body(name string) {
	s.mu.Lock()
	s.testRuns[name]++
	if ch, ok := s.started[name]; ok {
		select {
		case <-ch:
		default:
			close(ch)
		}
	}
	hang := s.hangCtx[name]
	release := s.hold[name]
	skip := s.skipTests[name]
	doPanic := s.panicTests[name]
	fatal := s.fatalTests[name]
	fail := s.errorTests[name]
	ctx := s.ctx
	s.mu.Unlock()

	if release != nil {
		<-release
	}
	if hang {
		<-ctx.Done()
		return
	}
	if skip {
		s.T().Skip("skipping " + name)
	}
	if doPanic {
		panic("panic-" + name)
	}
	if fatal {
		s.T().Fatal("fatal-" + name)
	}
	if fail {
		s.T().Error("error-" + name)
	}
}

func (s *recSessionSuite) runs(name string) int {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.testRuns[name]
}

func (s *recSessionSuite) TestAlpha() { s.body("TestAlpha") }
func (s *recSessionSuite) TestBeta()  { s.body("TestBeta") }
func (s *recSessionSuite) TestGamma() { s.body("TestGamma") }

func depsMap() map[string][]string {
	return map[string][]string{"TestGamma": {"TestBeta"}}
}

func TestRecoverPlanBuild(t *testing.T) {
	rec := &recoverCallRecorder{}
	s := newRecSessionSuite(rec)

	plan, err := BuildPlan(s, WithDependencies(depsMap()))
	require.NoError(t, err)

	assert.Equal(t, "recSessionSuite", plan.SuiteName())
	assert.NotEmpty(t, plan.ID())
	assert.Len(t, plan.Tests(), 3)
	assert.Equal(t, []string{"TestAlpha", "TestBeta", "TestGamma"},
		[]string{plan.tests[0].name, plan.tests[1].name, plan.tests[2].name})

	gamma, ok := plan.Test("TestGamma")
	require.True(t, ok)
	assert.Equal(t, []string{"TestBeta"}, gamma.DependsOn())
	assert.Equal(t, 2, gamma.Index())

	var stages []HookStage
	for _, f := range plan.Fixtures() {
		stages = append(stages, f.Stage)
	}
	assert.Equal(t, []HookStage{
		StageSetupSuite, StageTearDownSuite, StageSetupTest, StageBeforeTest,
		StageAfterTest, StageTearDownTest,
	}, stages)
	assert.Equal(t, ScopeSuite, plan.fixtures[0].Scope)
	assert.Equal(t, ScopeTest, plan.fixtures[2].Scope)

	// Getters return copies: mutating them cannot change the plan.
	tests := plan.Tests()
	tests[0] = nil
	fixtures := gamma.Fixtures()
	fixtures[0] = PlannedFixture{}
	deps := gamma.DependsOn()
	deps[0] = "hacked"
	assert.Equal(t, "TestAlpha", plan.tests[0].name)
	assert.Len(t, gamma.fixtures, 4)
	assert.Equal(t, "TestBeta", gamma.dependsOn[0])

	// Same configuration produces the same fingerprint.
	again, err := BuildPlan(newRecSessionSuite(rec), WithDependencies(depsMap()))
	require.NoError(t, err)
	assert.Equal(t, plan.ID(), again.ID())

	// Filter or dependencies change the fingerprint.
	filtered, err := BuildPlan(newRecSessionSuite(rec), WithFilter("Alpha"))
	require.NoError(t, err)
	assert.NotEqual(t, plan.ID(), filtered.ID())
	assert.Len(t, filtered.Tests(), 1)

	noDeps, err := BuildPlan(newRecSessionSuite(rec))
	require.NoError(t, err)
	assert.NotEqual(t, plan.ID(), noDeps.ID())
}

func TestRecoverPlanValidation(t *testing.T) {
	rec := &recoverCallRecorder{}

	_, err := BuildPlan(newRecSessionSuite(rec), WithFilter("("))
	assert.True(t, errors.Is(err, ErrInvalidPlan), "got %v", err)

	_, err = BuildPlan(newRecSessionSuite(rec), WithDependencies(map[string][]string{
		"TestAlpha": {"TestMissing"},
	}))
	assert.True(t, errors.Is(err, ErrInvalidPlan), "unknown dependency: %v", err)

	_, err = BuildPlan(newRecSessionSuite(rec), WithDependencies(map[string][]string{
		"TestAlpha": {"TestAlpha"},
	}))
	assert.True(t, errors.Is(err, ErrInvalidPlan), "self dependency: %v", err)

	_, err = BuildPlan(newRecSessionSuite(rec), WithDependencies(map[string][]string{
		"TestAlpha": {"TestBeta"},
		"TestBeta":  {"TestAlpha"},
	}))
	assert.True(t, errors.Is(err, ErrInvalidPlan), "cycle: %v", err)

	_, err = BuildPlan(newRecSessionSuite(rec), WithFilter("NothingMatches"))
	assert.True(t, errors.Is(err, ErrInvalidPlan), "empty selection: %v", err)
}

func TestRecoverPlanMismatch(t *testing.T) {
	rec := &recoverCallRecorder{}
	plan, err := BuildPlan(newRecSessionSuite(rec))
	require.NoError(t, err)

	tamperedID := *plan
	tamperedID.id = "0000000000000000000000000000000000000000000000000000000000000000"
	_, err = NewRunSession(t, &tamperedID, newRecSessionSuite(rec))
	assert.True(t, errors.Is(err, ErrPlanMismatch), "tampered id: %v", err)

	tamperedTest := *plan
	tamperedTest.tests = append([]*PlannedTest(nil), plan.tests...)
	hacked := *plan.tests[0]
	hacked.name = "TestHacked"
	tamperedTest.tests[0] = &hacked
	tamperedTest.byName = map[string]*PlannedTest{"TestHacked": &hacked}
	tamperedTest.id = "1111111111111111111111111111111111111111111111111111111111111111"
	_, err = NewRunSession(t, &tamperedTest, newRecSessionSuite(rec))
	assert.True(t, errors.Is(err, ErrPlanMismatch), "tampered method set: %v", err)

	tamperedFilter := *plan
	tamperedFilter.filter = "TestBeta"
	_, err = NewRunSession(t, &tamperedFilter, newRecSessionSuite(rec))
	assert.True(t, errors.Is(err, ErrPlanMismatch), "tampered filter: %v", err)
}

func TestRecoverFirstRunLifecycle(t *testing.T) {
	rec := &recoverCallRecorder{}
	ok := runRecoverIsolated(t, "FirstRun", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		plan, err := BuildPlan(s)
		require.NoError(t, err)
		session, err := NewRunSession(t, plan, s)
		require.NoError(t, err)
		require.NoError(t, session.Run())
		require.NoError(t, session.Close())

		expected := []string{
			"SetupSuite",
			"SetupTest", "BeforeTest:TestAlpha", "AfterTest:TestAlpha", "TearDownTest",
			"SetupTest", "BeforeTest:TestBeta", "AfterTest:TestBeta", "TearDownTest",
			"SetupTest", "BeforeTest:TestGamma", "AfterTest:TestGamma", "TearDownTest",
			"TearDownSuite",
		}
		assert.Equal(t, expected, rec.snapshot())
		result := session.Result()
		require.Len(t, result.Runs, 1)
		assert.Equal(t, runKindInitial, result.Runs[0].Kind)
		assert.Len(t, result.Runs[0].Tests, 3)
		for _, a := range result.Runs[0].Tests {
			assert.Equal(t, StatusPassed, a.Status)
		}
	})
	assert.True(t, ok, "passing suite must report success")
	assert.Equal(t, 1, rec.count("SetupSuite"))
	assert.Equal(t, 1, rec.count("TearDownSuite"))
	assert.Equal(t, 3, rec.count("SetupTest"))
	assert.Equal(t, 3, rec.count("TearDownTest"))
}

func TestRecoverSkipSemantics(t *testing.T) {
	rec := &recoverCallRecorder{}
	ok := runRecoverIsolated(t, "Skip", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		s.skipTests["TestBeta"] = true
		plan, err := BuildPlan(s)
		require.NoError(t, err)
		session, err := NewRunSession(t, plan, s)
		require.NoError(t, err)
		require.NoError(t, session.Run())
		require.NoError(t, session.Close())

		latest, ok := session.Result().Latest("TestBeta")
		require.True(t, ok)
		assert.Equal(t, StatusSkipped, latest.Status)
		assert.Equal(t, 1, rec.count("BeforeTest:TestBeta"))
		assert.Equal(t, 1, rec.count("AfterTest:TestBeta"))
		assert.Equal(t, 3, rec.count("SetupTest"))
		assert.Equal(t, 3, rec.count("TearDownTest"))
	})
	assert.True(t, ok, "a skipped subtest is a successful go test outcome")
}

func TestRecoverFailureAndRerun(t *testing.T) {
	rec := &recoverCallRecorder{}
	ok := runRecoverIsolated(t, "Rerun", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		s.errorTests["TestAlpha"] = true
		plan, err := BuildPlan(s)
		require.NoError(t, err)
		session, err := NewRunSession(t, plan, s)
		require.NoError(t, err)
		require.NoError(t, session.Run())

		original, ok := session.Result().OriginalFailure("TestAlpha")
		require.True(t, ok)
		assert.Equal(t, StatusFailed, original.Status)
		firstRunID := original.RunID

		// Rerunning a non-failed test or an unknown name is rejected.
		assert.True(t, errors.Is(session.Rerun("TestBeta"), ErrRerunTarget))
		assert.True(t, errors.Is(session.Rerun("TestNope"), ErrRerunTarget))
		setupBefore := s.setupN
		assert.True(t, errors.Is(session.Rerun("TestAlpha", "TestAlpha"), ErrRerunTarget))
		assert.Equal(t, setupBefore, s.setupN, "rejected rerun has no fixture side effects")

		// Rerun before any initial run on a fresh session is rejected.
		other, err := NewRunSession(t, plan, newRecSessionSuite(rec), WithStore(NewMemoryStore()))
		require.NoError(t, err)
		assert.True(t, errors.Is(other.Rerun("TestAlpha"), ErrRerunInProgress))
		require.NoError(t, other.Close())

		// Fix the failure and rerun only TestAlpha against the same plan.
		s.errorTests["TestAlpha"] = false
		require.NoError(t, session.Rerun("TestAlpha"))

		attempts := session.Result().Attempts("TestAlpha")
		require.Len(t, attempts, 2)
		assert.Equal(t, StatusFailed, attempts[0].Status)
		assert.Equal(t, StatusPassed, attempts[1].Status)
		assert.Equal(t, 1, attempts[0].Attempt)
		assert.Equal(t, 2, attempts[1].Attempt)
		assert.NotEqual(t, firstRunID, attempts[1].RunID)
		assert.Equal(t, 2, s.runs("TestAlpha"), "rerun executes the test body again")
		assert.Equal(t, 1, rec.count("SetupSuite"), "suite fixture is not repeated")
		assert.Equal(t, 1, s.runs("TestBeta"))
		assert.Equal(t, 4, s.setupN, "rerun uses fresh test-scoped state")
		assert.Equal(t, 4, s.teardownN)

		// A passed test cannot be rerun and the plan cannot be fully resubmitted.
		assert.True(t, errors.Is(session.Rerun("TestAlpha"), ErrRerunTarget))
		assert.True(t, errors.Is(session.Run(), ErrPlanAlreadyRun))
		assert.Equal(t, 4, s.setupN, "resubmission consumes no state")

		require.NoError(t, session.Close())
	})
	assert.False(t, ok, "the initial failed subtest must still fail the go test")
}

func TestRecoverHookPanics(t *testing.T) {
	// For the failing TestBeta (2nd in order): expected call counts.
	cases := []struct {
		name         string
		configure    func(s *recSessionSuite)
		wantSentinel error
		beforeBeta   int
		afterBeta    int
		runsBeta     int
	}{
		{"SetupTest", func(s *recSessionSuite) { s.panicHookAt[StageSetupTest] = 2 }, ErrFixtureInit, 0, 1, 0},
		{"BeforeTest", func(s *recSessionSuite) { s.panicHookAt[StageBeforeTest] = 2 }, ErrFixtureInit, 1, 1, 0},
		{"AfterTest", func(s *recSessionSuite) { s.panicHookAt[StageAfterTest] = 2 }, ErrFixtureCleanup, 1, 1, 1},
		{"TearDownTest", func(s *recSessionSuite) { s.panicHookAt[StageTearDownTest] = 2 }, ErrFixtureCleanup, 1, 1, 1},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			rec := &recoverCallRecorder{}
			var runErr error
			ok := runRecoverIsolated(t, tc.name, func(t *testing.T) {
				s := newRecSessionSuite(rec)
				tc.configure(s)
				plan, err := BuildPlan(s)
				require.NoError(t, err)
				session, err := NewRunSession(t, plan, s)
				require.NoError(t, err)
				runErr = session.Run()

				var le *LifecycleError
				require.True(t, errors.As(runErr, &le), "got %v", runErr)
				assert.Equal(t, tc.beforeBeta, rec.count("BeforeTest:TestBeta"))
				assert.Equal(t, tc.afterBeta, rec.count("AfterTest:TestBeta"))
				assert.Equal(t, tc.runsBeta, s.runs("TestBeta"))
				require.NoError(t, session.Close())
			})
			assert.False(t, ok)
			assert.True(t, errors.Is(runErr, tc.wantSentinel),
				"%s: want %v, got %v", tc.name, tc.wantSentinel, runErr)
		})
	}

	// require-style FailNow (runtime.Goexit) in SetupTest is an init failure
	// and cleanup hooks still run exactly once.
	var ok bool
	rec := &recoverCallRecorder{}
	var fatalHookErr error
	ok = runRecoverIsolated(t, "SetupTestFatal", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		s.fatalHookAt[StageSetupTest] = 2
		plan, _ := BuildPlan(s)
		session, _ := NewRunSession(t, plan, s)
		fatalHookErr = session.Run()
		assert.Equal(t, 1, rec.count("AfterTest:TestBeta"))
		assert.Equal(t, 3, s.teardownN)
		assert.Equal(t, 0, s.runs("TestBeta"))
		_ = session.Close()
	})
	assert.False(t, ok)
	assert.True(t, errors.Is(fatalHookErr, ErrFixtureInit), "got %v", fatalHookErr)

	// Test-body panic: outcome is a test failure, not a fixture failure.
	rec = &recoverCallRecorder{}
	var bodyErr error
	ok = runRecoverIsolated(t, "BodyPanic", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		s.panicTests["TestBeta"] = true
		plan, _ := BuildPlan(s)
		session, _ := NewRunSession(t, plan, s)
		bodyErr = session.Run()
		latest, _ := session.Result().Latest("TestBeta")
		assert.Equal(t, StatusPanicked, latest.Status)
		assert.Equal(t, StageTest, latest.FailureStage)
		assert.Equal(t, 1, rec.count("AfterTest:TestBeta"))
		assert.Equal(t, 3, s.teardownN, "TearDownTest runs once for every test")
		_ = session.Close()
	})
	assert.False(t, ok)
	assert.NoError(t, bodyErr, "body panics are reported through testing.T only")
}

func TestRecoverSuiteFixtures(t *testing.T) {
	// Panic in SetupSuite: no test, no TearDownSuite; Run may be retried.
	rec := &recoverCallRecorder{}
	var setupErr error
	ok := runRecoverIsolated(t, "SetupSuitePanic", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		s.panicSetup = true
		plan, _ := BuildPlan(s)
		session, err := NewRunSession(t, plan, s)
		require.NoError(t, err)
		setupErr = session.Run()
		assert.True(t, errors.Is(session.Rerun("TestAlpha"), ErrRerunInProgress))
		// Explicitly close before cleanup: SetupSuite failed, so no teardown.
		require.NoError(t, session.Close())
	})
	assert.False(t, ok)
	assert.True(t, errors.Is(setupErr, ErrFixtureInit), "got %v", setupErr)
	assert.Equal(t, 0, rec.count("SetupTest"))
	assert.Equal(t, 0, rec.count("TearDownSuite"))

	// Panic in TearDownSuite surfaces through Close.
	rec = &recoverCallRecorder{}
	var closeErr error
	ok = runRecoverIsolated(t, "TearDownSuitePanic", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		s.panicTeard = true
		plan, _ := BuildPlan(s)
		session, _ := NewRunSession(t, plan, s)
		require.NoError(t, session.Run())
		closeErr = session.Close()
		assert.True(t, errors.Is(session.Close(), ErrSessionClosed))
	})
	assert.False(t, ok)
	assert.True(t, errors.Is(closeErr, ErrFixtureCleanup), "got %v", closeErr)
	assert.Equal(t, 1, rec.count("TearDownSuite"), "TearDownSuite runs at most once")

	// Skip in SetupSuite: session is skipped, TearDownSuite does not run.
	rec = &recoverCallRecorder{}
	ok = runRecoverIsolated(t, "SetupSuiteSkip", func(t *testing.T) {
		s := &skipSetupSuite{rec: rec}
		plan, err := BuildPlan(s)
		require.NoError(t, err)
		session, err := NewRunSession(t, plan, s)
		require.NoError(t, err)
		session.Run()
		t.Fatal("Run must not return after SetupSuite skips")
	})
	assert.True(t, ok, "the whole enclosing test should be skipped: %v", ok)
	assert.Equal(t, 0, rec.count("TearDownSuite"))
}

type skipSetupSuite struct {
	Suite
	rec *recoverCallRecorder
}

func (s *skipSetupSuite) SetupSuite()    { s.T().Skip("skip suite") }
func (s *skipSetupSuite) TearDownSuite() { s.rec.add("TearDownSuite") }
func (s *skipSetupSuite) TestSomething() {}

func TestRecoverTimeout(t *testing.T) {
	rec := &recoverCallRecorder{}
	var runErr error
	ok := runRecoverIsolated(t, "Timeout", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		s.hangCtx["TestBeta"] = true
		plan, _ := BuildPlan(s)
		session, _ := NewRunSession(t, plan, s, WithTestTimeout(50*time.Millisecond))
		start := time.Now()
		runErr = session.Run()
		elapsed := time.Since(start)

		assert.True(t, errors.Is(runErr, ErrTestTimeout), "got %v", runErr)
		var te *TimeoutError
		require.True(t, errors.As(runErr, &te))
		assert.Equal(t, "TestBeta", te.TestName)
		assert.Less(t, elapsed, 2*time.Second)

		beta, _ := session.Result().Latest("TestBeta")
		assert.Equal(t, StatusTimeout, beta.Status)
		gamma, _ := session.Result().Latest("TestGamma")
		assert.Equal(t, StatusCanceled, gamma.Status)
		assert.Equal(t, 2, s.setupN, "Alpha ran and Beta started; Gamma never got fixtures")
		assert.Equal(t, 2, s.teardownN, "Beta cleaned exactly once")
		assert.Equal(t, 0, s.runs("TestGamma"))

		// The timed-out test is rerunnable; canceled tests are not.
		s.hangCtx["TestBeta"] = false
		require.NoError(t, session.Rerun("TestBeta"))
		latest, _ := session.Result().Latest("TestBeta")
		assert.Equal(t, StatusPassed, latest.Status)
		assert.True(t, errors.Is(session.Rerun("TestGamma"), ErrRerunTarget))
		_ = session.Close()
	})
	assert.False(t, ok)
}

func TestRecoverCancel(t *testing.T) {
	rec := &recoverCallRecorder{}
	var runErr error
	ok := runRecoverIsolated(t, "Cancel", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		started := make(chan struct{})
		s.started["TestAlpha"] = started
		s.hangCtx["TestAlpha"] = true
		plan, _ := BuildPlan(s)
		ctx, cancel := context.WithCancel(context.Background())
		session, _ := NewRunSession(t, plan, s, WithContext(ctx))

		var wg sync.WaitGroup
		wg.Add(1)
		go func() {
			defer wg.Done()
			runErr = session.Run()
		}()
		<-started
		cancel()
		wg.Wait()

		assert.True(t, errors.Is(runErr, ErrRunCanceled), "got %v", runErr)
		alpha, _ := session.Result().Latest("TestAlpha")
		assert.Equal(t, StatusCanceled, alpha.Status)
		for _, name := range []string{"TestBeta", "TestGamma"} {
			a, found := session.Result().Latest(name)
			require.True(t, found)
			assert.Equal(t, StatusCanceled, a.Status, name)
		}
		assert.Equal(t, 1, s.setupN, "only the in-flight test got fixtures")
		assert.Equal(t, 1, s.teardownN)
		require.NoError(t, session.Close())
		assert.Equal(t, 1, rec.count("TearDownSuite"))
	})
	assert.True(t, ok, "cancellation is reported through the returned error, not as a test failure")
}

func TestRecoverConcurrentRerun(t *testing.T) {
	rec := &recoverCallRecorder{}
	ok := runRecoverIsolated(t, "Concurrent", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		s.errorTests["TestAlpha"] = true
		release := make(chan struct{})
		started := make(chan struct{})
		s.hold["TestBeta"] = release
		s.started["TestBeta"] = started

		plan, _ := BuildPlan(s)
		session, _ := NewRunSession(t, plan, s)

		var wg sync.WaitGroup
		wg.Add(1)
		go func() {
			defer wg.Done()
			_ = session.Run()
		}()
		<-started

		err := session.Rerun("TestAlpha")
		assert.True(t, errors.Is(err, ErrConcurrentRun), "rerun during run: %v", err)
		err = session.Run()
		assert.True(t, errors.Is(err, ErrConcurrentRun), "run during run: %v", err)

		close(release)
		wg.Wait()
		_ = session.Close()
	})
	assert.False(t, ok)
}

func TestRecoverDependencyGate(t *testing.T) {
	rec := &recoverCallRecorder{}
	ok := runRecoverIsolated(t, "Dependencies", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		s.errorTests["TestBeta"] = true
		plan, err := BuildPlan(s, WithDependencies(depsMap()))
		require.NoError(t, err)
		session, err := NewRunSession(t, plan, s)
		require.NoError(t, err)
		require.NoError(t, session.Run())

		gamma, found := session.Result().Latest("TestGamma")
		require.True(t, found)
		assert.Equal(t, StatusSkipped, gamma.Status)
		assert.Equal(t, StageDependency, gamma.FailureStage)
		assert.Equal(t, 0, s.runs("TestGamma"), "skipped dependent does not run")

		// Fix the dependency and rerun it; then the dependent can run too.
		s.errorTests["TestBeta"] = false
		require.NoError(t, session.Rerun("TestBeta"))
		require.NoError(t, session.Rerun("TestGamma"))
		beta := session.Result().Attempts("TestBeta")
		require.Len(t, beta, 2)
		assert.Equal(t, StatusFailed, beta[0].Status)
		assert.Equal(t, StatusPassed, beta[1].Status)
		gammaAttempts := session.Result().Attempts("TestGamma")
		require.Len(t, gammaAttempts, 2)
		assert.Equal(t, StatusSkipped, gammaAttempts[0].Status)
		assert.Equal(t, StatusPassed, gammaAttempts[1].Status)

		_ = session.Close()
	})
	assert.False(t, ok)
}

func TestRecoverResumeFromStore(t *testing.T) {
	store := NewMemoryStore()
	rec := &recoverCallRecorder{}

	ok := runRecoverIsolated(t, "SessionOne", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		s.errorTests["TestAlpha"] = true
		plan, err := BuildPlan(s)
		require.NoError(t, err)
		session, err := NewRunSession(t, plan, s, WithStore(store))
		require.NoError(t, err)
		require.NoError(t, session.Run())
		require.NoError(t, session.Close())
	})
	assert.False(t, ok)
	assert.Equal(t, 1, rec.count("SetupSuite"))

	ok = runRecoverIsolated(t, "SessionTwo", func(t *testing.T) {
		s := newRecSessionSuite(rec) // fresh instance, new test-level state
		plan, err := BuildPlan(s, WithDependencies(nil))
		require.NoError(t, err)
		session, err := NewRunSession(t, plan, s, WithStore(store))
		require.NoError(t, err)

		// The same plan cannot be fully consumed again.
		assert.True(t, errors.Is(session.Run(), ErrPlanAlreadyRun))
		assert.Equal(t, 1, rec.count("SetupSuite"), "rejected resubmission has no side effects")

		// Rerun the failed test from the recovered history.
		require.NoError(t, session.Rerun("TestAlpha"))
		attempts := session.Result().Attempts("TestAlpha")
		require.Len(t, attempts, 2)
		assert.Equal(t, StatusFailed, attempts[0].Status, "original failure is preserved")
		assert.Equal(t, StatusPassed, attempts[1].Status, "rerun result is linked")
		assert.Equal(t, plan.ID(), session.Plan().ID())
		require.NoError(t, session.Close())
	})
	assert.True(t, ok, "the resumed session reruns the test successfully: %v", ok)
	assert.Equal(t, 2, rec.count("SetupSuite"), "new session runs suite fixtures again")
	assert.Equal(t, 2, rec.count("TearDownSuite"))
}

func TestRecoverFileStore(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "session.json")
	rec := &recoverCallRecorder{}

	ok := runRecoverIsolated(t, "FileSessionOne", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		s.fatalTests["TestAlpha"] = true
		plan, _ := BuildPlan(s)
		session, err := NewRunSession(t, plan, s, WithStore(NewFileStore(path)))
		require.NoError(t, err)
		require.NoError(t, session.Run())
		require.NoError(t, session.Close())
	})
	assert.False(t, ok)

	ok = runRecoverIsolated(t, "FileSessionTwo", func(t *testing.T) {
		s := newRecSessionSuite(rec)
		plan, _ := BuildPlan(s)
		session, err := NewRunSession(t, plan, s, WithStore(NewFileStore(path)))
		require.NoError(t, err)
		require.NoError(t, session.Rerun("TestAlpha"))
		latest, ok := session.Result().Latest("TestAlpha")
		require.True(t, ok)
		assert.Equal(t, StatusPassed, latest.Status)
		require.NoError(t, session.Close())
	})
	assert.True(t, ok)

	// Garbage record: corrupted.
	require.NoError(t, os.WriteFile(path, []byte("{not-json"), 0o600))
	_, err := NewRunSession(t, mustPlan(t, rec), newRecSessionSuite(rec), WithStore(NewFileStore(path)))
	assert.True(t, errors.Is(err, ErrCorruptedResult), "garbage: %v", err)

	// Semantically invalid record with a valid envelope checksum: corrupted.
	corruptStoredSession(t, path)
	_, err = NewRunSession(t, mustPlan(t, rec), newRecSessionSuite(rec), WithStore(NewFileStore(path)))
	assert.True(t, errors.Is(err, ErrCorruptedResult), "semantic: %v", err)
}

func TestRecoverStaleSave(t *testing.T) {
	rec := &recoverCallRecorder{}
	plan := mustPlan(t, rec)
	store := NewMemoryStore()
	s := newRecSessionSuite(rec)
	session, err := NewRunSession(t, plan, s, WithStore(store))
	require.NoError(t, err)
	require.NoError(t, session.Run())
	require.NoError(t, session.Close())

	// A save carrying an already-used version is rejected, not applied.
	st, found, err := store.Load(plan.ID())
	require.NoError(t, err)
	require.True(t, found)
	stale := cloneState(st)
	stale.Version = st.Version // not bumped
	err = store.Save(plan.ID(), stale)
	assert.True(t, errors.Is(err, ErrCorruptedResult), "got %v", err)
}

// flakyStore fails every Save after failAfter successful ones.
type flakyStore struct {
	ResultStore
	saves     int
	failAfter int
}

func (f *flakyStore) Save(planID string, st *storedState) error {
	f.saves++
	if f.saves > f.failAfter {
		return &CorruptionError{Detail: "forced store failure"}
	}
	return f.ResultStore.Save(planID, st)
}

func TestRecoverStoreFailure(t *testing.T) {
	ok := runRecoverIsolated(t, "StoreFailure", func(t *testing.T) {
		rec := &recoverCallRecorder{}
		plan := mustPlan(t, rec)
		store := &flakyStore{ResultStore: NewMemoryStore(), failAfter: 1}
		s := newRecSessionSuite(rec)
		session, err := NewRunSession(t, plan, s, WithStore(store))
		require.NoError(t, err)

		// The second save (run start) fails before any fixture side effect.
		runErr := session.Run()
		assert.True(t, errors.Is(runErr, ErrCorruptedResult), "got %v", runErr)
		assert.Equal(t, 0, s.setupN)
		assert.Equal(t, 0, s.teardownN)

		// The session is poisoned: resubmission returns the same error and
		// produces no new side effects instead of replaying the plan.
		againErr := session.Run()
		assert.True(t, errors.Is(againErr, ErrCorruptedResult), "got %v", againErr)
		assert.Equal(t, 0, s.setupN)
		assert.Equal(t, 0, s.teardownN)

		// SetupSuite never succeeded, so Close performs no suite teardown;
		// the failed final save is surfaced from Close too.
		closeErr := session.Close()
		assert.True(t, errors.Is(closeErr, ErrCorruptedResult), "got %v", closeErr)
		assert.Equal(t, 0, rec.count("TearDownSuite"))
	})
	assert.True(t, ok)

	// Failure during the run aborts before remaining tests: the plan is not
	// marked consumed, but suite fixtures are still torn down exactly once.
	ok = runRecoverIsolated(t, "StoreFailureMidRun", func(t *testing.T) {
		rec := &recoverCallRecorder{}
		plan := mustPlan(t, rec)
		store := &flakyStore{ResultStore: NewMemoryStore(), failAfter: 2}
		s := newRecSessionSuite(rec)
		session, err := NewRunSession(t, plan, s, WithStore(store))
		require.NoError(t, err)

		runErr := session.Run()
		assert.True(t, errors.Is(runErr, ErrCorruptedResult), "got %v", runErr)
		assert.Equal(t, 1, s.setupN, "only TestAlpha executed")
		assert.Equal(t, 1, s.teardownN)
		_, gammaRan := session.Result().Latest("TestGamma")
		assert.False(t, gammaRan)

		assert.True(t, errors.Is(session.Run(), ErrCorruptedResult))
		assert.True(t, errors.Is(session.Rerun("TestBeta"), ErrRerunInProgress))

		// TearDownSuite still runs exactly once even though the final save
		// keeps failing; the failure is surfaced from Close.
		closeErr := session.Close()
		assert.True(t, errors.Is(closeErr, ErrCorruptedResult), "got %v", closeErr)
		assert.Equal(t, 1, rec.count("SetupSuite"))
		assert.Equal(t, 1, rec.count("TearDownSuite"))
	})
	assert.True(t, ok)
}

func TestRecoverInvalidSignature(t *testing.T) {
	ok := runRecoverIsolated(t, "InvalidSignature", func(t *testing.T) {
		s := &badSignatureRecoverSuite{}
		plan, err := BuildPlan(s)
		require.NoError(t, err)
		var invalid []string
		for _, pt := range plan.Tests() {
			if pt.InvalidSignature() != "" {
				invalid = append(invalid, pt.Name())
			}
		}
		assert.Equal(t, []string{"TestBad"}, invalid)
		session, err := NewRunSession(t, plan, s)
		require.NoError(t, err)
		require.NoError(t, session.Run())
		latest, ok := session.Result().Latest("TestBad")
		require.True(t, ok)
		assert.Equal(t, StatusFailed, latest.Status)
		assert.Equal(t, StageSignature, latest.FailureStage)
		_ = session.Close()
	})
	assert.False(t, ok)
}

type badSignatureRecoverSuite struct {
	Suite
}

func (s *badSignatureRecoverSuite) TestGood() {}
func (s *badSignatureRecoverSuite) TestBad(unexpected string) {
	_ = unexpected
}

func mustPlan(t *testing.T, rec *recoverCallRecorder) *TestPlan {
	t.Helper()
	plan, err := BuildPlan(newRecSessionSuite(rec))
	require.NoError(t, err)
	return plan
}

// corruptStoredSession writes an envelope whose payload passes the checksum
// but contains an unknown attempt status.
func corruptStoredSession(t *testing.T, path string) {
	t.Helper()
	st := &storedState{
		Version:  1,
		PlanID:   "x",
		Consumed: false,
		Runs:     []storedRun{{ID: "r1", Kind: runKindInitial, Start: time.Now(), End: time.Now()}},
		Attempts: map[string][]storedAttempt{
			"TestAlpha": {{
				RunID: "r1", Attempt: 1, TestName: "TestAlpha",
				Status: AttemptStatus("weird"), Start: time.Now(), End: time.Now(),
			}},
		},
	}
	payload, err := json.Marshal(st)
	require.NoError(t, err)
	sum := sha256.Sum256(payload)
	env := fileEnvelope{
		Version:  1,
		Payload:  base64.StdEncoding.EncodeToString(payload),
		Checksum: hex.EncodeToString(sum[:]),
	}
	raw, err := json.Marshal(&env)
	require.NoError(t, err)
	require.NoError(t, os.WriteFile(path, raw, 0o600))
}
