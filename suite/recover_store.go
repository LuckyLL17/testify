package suite

import (
	"bytes"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sync"
	"time"
)

// ResultStore persists the correlated execution state of a plan. Save calls
// are compare-and-swap on the record version: a stale write fails instead of
// overwriting newer state. Implementations must be safe for concurrent use.
type ResultStore interface {
	// Load returns the stored state. found is false when nothing was stored
	// for the plan yet.
	Load(planID string) (state *storedState, found bool, err error)
	// Save stores state. The first save must carry version 1; subsequent
	// saves must carry exactly previousVersion+1.
	Save(planID string, state *storedState) error
}

// storedAttempt is the persisted record of one test execution.
type storedAttempt struct {
	RunID        string        `json:"run_id"`
	Attempt      int           `json:"attempt"`
	TestName     string        `json:"test_name"`
	Status       AttemptStatus `json:"status"`
	FailureStage HookStage     `json:"failure_stage,omitempty"`
	Failure      string        `json:"failure,omitempty"`
	Start        time.Time     `json:"start"`
	End          time.Time     `json:"end"`

	// hookErrs is transient: it surfaces cleanup failures through Run/Rerun
	// return values but is not part of the durable record.
	hookErrs []*LifecycleError `json:"-"`
}

// lifecycleErrors translates a stored attempt into distinguishable fixture
// errors. Test-body failures (stage Test) are reported through testing.T only.
func (a storedAttempt) lifecycleErrors() []*LifecycleError {
	var out []*LifecycleError
	out = append(out, a.hookErrs...)
	if a.Status == StatusFailed {
		switch a.FailureStage {
		case StageSetupTest, StageBeforeTest:
			out = append(out, &LifecycleError{
				Stage:    a.FailureStage,
				TestName: a.TestName,
				Message:  a.Failure,
			})
		}
	}
	return out
}

// storedRun is the persisted record of one initial run or one rerun.
type storedRun struct {
	ID      string    `json:"id"`
	Kind    string    `json:"kind"`
	Targets []string  `json:"targets,omitempty"`
	Start   time.Time `json:"start"`
	End     time.Time `json:"end"`
}

// storedState is the durable session record.
type storedState struct {
	Version  int                        `json:"version"`
	PlanID   string                     `json:"plan_id"`
	Consumed bool                       `json:"consumed"`
	Runs     []storedRun                `json:"runs"`
	Attempts map[string][]storedAttempt `json:"attempts"`
}

func cloneState(in *storedState) *storedState {
	raw, err := json.Marshal(in)
	if err != nil {
		// All fields are JSON-safe in practice; fail loudly rather than lose
		// correlation data.
		panic(fmt.Sprintf("testify/suite: internal state encoding failure: %v", err))
	}
	out := &storedState{}
	if err := json.Unmarshal(raw, out); err != nil {
		panic(fmt.Sprintf("testify/suite: internal state decoding failure: %v", err))
	}
	return out
}

// validateState performs structural integrity checks that need no plan.
func validateState(st *storedState) error {
	if st == nil {
		return &CorruptionError{Detail: "missing record"}
	}
	if st.PlanID == "" {
		return &CorruptionError{Detail: "missing plan id"}
	}
	if st.Version < 1 {
		return &CorruptionError{Detail: "invalid record version"}
	}
	if st.Attempts == nil {
		return &CorruptionError{Detail: "missing attempts table"}
	}

	runIndex := map[string]int{}
	sawInitial := false
	for i, r := range st.Runs {
		if r.ID == "" {
			return &CorruptionError{Detail: fmt.Sprintf("run #%d has no id", i+1)}
		}
		if _, dup := runIndex[r.ID]; dup {
			return &CorruptionError{Detail: "duplicated run id " + r.ID}
		}
		runIndex[r.ID] = i
		switch r.Kind {
		case runKindInitial:
			if i != 0 || sawInitial {
				return &CorruptionError{Detail: "initial run must be the single first run"}
			}
			sawInitial = true
			if len(r.Targets) != 0 {
				return &CorruptionError{Detail: "initial run must not carry rerun targets"}
			}
		case runKindRerun:
			if !sawInitial {
				return &CorruptionError{Detail: fmt.Sprintf("rerun %q precedes initial run", r.ID)}
			}
			if len(r.Targets) == 0 {
				return &CorruptionError{Detail: fmt.Sprintf("rerun %q has no targets", r.ID)}
			}
		default:
			return &CorruptionError{Detail: fmt.Sprintf("run %q has unknown kind %q", r.ID, r.Kind)}
		}
	}
	if st.Consumed && !sawInitial {
		return &CorruptionError{Detail: "consumed record has no initial run"}
	}

	attemptsByRun := map[string]int{}
	for name, list := range st.Attempts {
		if name == "" {
			return &CorruptionError{Detail: "attempt without test name"}
		}
		for i, a := range list {
			if a.Attempt != i+1 {
				return &CorruptionError{Detail: fmt.Sprintf("attempts of %q are not contiguous", name)}
			}
			if a.TestName != name {
				return &CorruptionError{Detail: fmt.Sprintf("attempt bucket %q contains attempt for %q", name, a.TestName)}
			}
			if _, ok := runIndex[a.RunID]; !ok {
				return &CorruptionError{Detail: fmt.Sprintf("attempt %d of %q references unknown run %q", a.Attempt, name, a.RunID)}
			}
			if err := validateAttempt(a); err != nil {
				return err
			}
			attemptsByRun[a.RunID]++
		}
	}
	return nil
}

func validateAttempt(a storedAttempt) error {
	switch a.Status {
	case StatusPassed:
		if a.FailureStage != "" {
			return &CorruptionError{Detail: "passed attempt " + a.TestName + " carries a failure stage"}
		}
	case StatusFailed:
		switch a.FailureStage {
		case StageSetupTest, StageBeforeTest, StageTest, StageAfterTest, StageTearDownTest, StageSignature:
		default:
			return &CorruptionError{Detail: "failed attempt " + a.TestName + " has invalid failure stage"}
		}
	case StatusPanicked, StatusTimeout:
		if a.FailureStage != StageTest {
			return &CorruptionError{Detail: string(a.Status) + " attempt " + a.TestName + " has invalid failure stage"}
		}
	case StatusSkipped:
		switch a.FailureStage {
		case "", StageDependency:
		default:
			return &CorruptionError{Detail: "skipped attempt " + a.TestName + " has invalid failure stage"}
		}
	case StatusCanceled:
		if a.FailureStage != "" && a.FailureStage != StageDependency {
			return &CorruptionError{Detail: "canceled attempt " + a.TestName + " has invalid failure stage"}
		}
	default:
		return &CorruptionError{Detail: fmt.Sprintf("attempt %d of %q has unknown status %q", a.Attempt, a.TestName, a.Status)}
	}
	if a.Start.IsZero() || a.End.IsZero() || a.End.Before(a.Start) {
		return &CorruptionError{Detail: fmt.Sprintf("attempt %d of %q has invalid timestamps", a.Attempt, a.TestName)}
	}
	return nil
}

// crossCheckState validates a structurally sound record against the plan it is
// about to be resumed with.
func crossCheckState(plan *TestPlan, st *storedState) error {
	if st.PlanID != plan.id {
		return &CorruptionError{Detail: "record belongs to a different plan"}
	}
	for name := range st.Attempts {
		if _, ok := plan.byName[name]; !ok {
			return &CorruptionError{Detail: "record contains unknown test " + name}
		}
	}
	for _, r := range st.Runs {
		seen := map[string]bool{}
		for _, target := range r.Targets {
			if _, ok := plan.byName[target]; !ok {
				return &CorruptionError{Detail: fmt.Sprintf("run %q targets unknown test %q", r.ID, target)}
			}
			if seen[target] {
				return &CorruptionError{Detail: fmt.Sprintf("run %q reruns %q twice", r.ID, target)}
			}
			seen[target] = true
		}
	}
	if st.Consumed {
		for _, pt := range plan.tests {
			if len(st.Attempts[pt.name]) == 0 {
				return &CorruptionError{Detail: "consumed record has no attempt for " + pt.name}
			}
		}
		for _, r := range st.Runs {
			expected := len(plan.tests)
			if r.Kind == runKindRerun {
				expected = len(r.Targets)
			}
			count := 0
			for _, list := range st.Attempts {
				for _, a := range list {
					if a.RunID == r.ID {
						count++
					}
				}
			}
			if count != expected {
				return &CorruptionError{Detail: fmt.Sprintf("run %q has %d attempts, expected %d", r.ID, count, expected)}
			}
		}
	}
	return nil
}

// NewMemoryStore returns a process-local ResultStore. Passing the same store
// to another session simulates recovery from a previous execution.
func NewMemoryStore() ResultStore {
	return &memoryStore{records: map[string][]byte{}}
}

type memoryStore struct {
	mu      sync.Mutex
	records map[string][]byte
}

func (m *memoryStore) Load(planID string) (*storedState, bool, error) {
	m.mu.Lock()
	raw, ok := m.records[planID]
	m.mu.Unlock()
	if !ok {
		return nil, false, nil
	}
	st := &storedState{}
	if err := json.Unmarshal(raw, st); err != nil {
		return nil, false, &CorruptionError{Detail: "record cannot be decoded: " + err.Error()}
	}
	return st, true, nil
}

func (m *memoryStore) Save(planID string, state *storedState) error {
	if state == nil {
		return &CorruptionError{Detail: "refusing to save nil record"}
	}
	raw, err := json.Marshal(state)
	if err != nil {
		return &CorruptionError{Detail: "record cannot be encoded: " + err.Error()}
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	existing, ok := m.records[planID]
	if err := checkCAS(existing, ok, state.Version); err != nil {
		return err
	}
	m.records[planID] = raw
	return nil
}

func checkCAS(existing []byte, found bool, version int) error {
	if !found {
		if version != 1 {
			return &CorruptionError{Detail: fmt.Sprintf("first save must use version 1, got %d", version)}
		}
		return nil
	}
	prev := &storedState{}
	if err := json.Unmarshal(existing, prev); err != nil {
		return &CorruptionError{Detail: "stored record cannot be decoded: " + err.Error()}
	}
	if version != prev.Version+1 {
		return &CorruptionError{Detail: fmt.Sprintf("stale save: record is at version %d, save carries %d", prev.Version, version)}
	}
	return nil
}

// fileEnvelope protects the JSON payload with a checksum so truncated or
// tampered records are reported as corrupted instead of silently applied.
type fileEnvelope struct {
	Version  int    `json:"version"`
	Payload  string `json:"payload"`
	Checksum string `json:"checksum"`
}

// NewFileStore returns a ResultStore backed by one JSON file. A missing file
// is an empty store. Writes are atomic.
func NewFileStore(path string) ResultStore {
	return &fileStore{path: path}
}

type fileStore struct {
	path string
	mu   sync.Mutex
}

func (f *fileStore) Load(planID string) (*storedState, bool, error) {
	f.mu.Lock()
	defer f.mu.Unlock()
	raw, err := os.ReadFile(f.path)
	if os.IsNotExist(err) {
		return nil, false, nil
	}
	if err != nil {
		return nil, false, err
	}
	st, err := decodeEnvelope(raw)
	if err != nil {
		return nil, false, err
	}
	if st.PlanID != planID {
		return nil, false, &CorruptionError{Detail: "file record belongs to a different plan"}
	}
	return st, true, nil
}

func (f *fileStore) Save(planID string, state *storedState) error {
	if state == nil {
		return &CorruptionError{Detail: "refusing to save nil record"}
	}
	f.mu.Lock()
	defer f.mu.Unlock()

	existingVersion, found := 0, false
	if raw, err := os.ReadFile(f.path); err == nil {
		prev, derr := decodeEnvelope(raw)
		if derr != nil {
			return derr
		}
		if prev.PlanID != planID {
			return &CorruptionError{Detail: "file record belongs to a different plan"}
		}
		existingVersion, found = prev.Version, true
	} else if !os.IsNotExist(err) {
		return err
	}
	if !found && state.Version != 1 {
		return &CorruptionError{Detail: fmt.Sprintf("first save must use version 1, got %d", state.Version)}
	}
	if found && state.Version != existingVersion+1 {
		return &CorruptionError{Detail: fmt.Sprintf("stale save: file is at version %d, save carries %d", existingVersion, state.Version)}
	}

	payload, err := json.Marshal(state)
	if err != nil {
		return &CorruptionError{Detail: "record cannot be encoded: " + err.Error()}
	}
	sum := sha256.Sum256(payload)
	env := fileEnvelope{
		Version:  1,
		Payload:  base64.StdEncoding.EncodeToString(payload),
		Checksum: hex.EncodeToString(sum[:]),
	}
	raw, err := json.MarshalIndent(&env, "", "  ")
	if err != nil {
		return err
	}
	dir := filepath.Dir(f.path)
	tmp, err := os.CreateTemp(dir, ".suite-session-*")
	if err != nil {
		return err
	}
	tmpName := tmp.Name()
	defer os.Remove(tmpName)
	if _, err := tmp.Write(raw); err != nil {
		tmp.Close()
		return err
	}
	if err := tmp.Close(); err != nil {
		return err
	}
	return os.Rename(tmpName, f.path)
}

func decodeEnvelope(raw []byte) (*storedState, error) {
	var env fileEnvelope
	if err := json.Unmarshal(raw, &env); err != nil {
		return nil, &CorruptionError{Detail: "record envelope is unreadable: " + err.Error()}
	}
	if env.Version != 1 {
		return nil, &CorruptionError{Detail: fmt.Sprintf("unsupported envelope version %d", env.Version)}
	}
	payload, err := base64.StdEncoding.DecodeString(env.Payload)
	if err != nil {
		return nil, &CorruptionError{Detail: "record payload is not valid base64"}
	}
	sum := sha256.Sum256(payload)
	if hex.EncodeToString(sum[:]) != env.Checksum {
		return nil, &CorruptionError{Detail: "record checksum mismatch"}
	}
	if bytes.IndexByte(payload, 0) >= 0 {
		return nil, &CorruptionError{Detail: "record payload contains illegal bytes"}
	}
	st := &storedState{}
	if err := json.Unmarshal(payload, st); err != nil {
		return nil, &CorruptionError{Detail: "record payload is unreadable: " + err.Error()}
	}
	return st, nil
}
