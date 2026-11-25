import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! Section 2.3. A bounded computation can be restarted without committing to hidden
costs across restarts. Internal moves and requests are separate small steps; the service
state persists between attempts. No decision tree or list of hidden cost assignments is
constructed by the computation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery

variable {P : Type*} {Q : Type*} {S : Type*} {O : Type*} {W : Type*}

/-- One move of the sign-recovery procedure. The two continuations accept one sign bit. -/
inductive Move (P Q O : Type*) where
  | done (value : O)
  | work (next : P)
  | query (q : Q) (negative positive : P)

/-- The result of one request to the geometric label service. -/
inductive Reply (S : Type*) where
  | answer (value : Bool) (state : S)
  | restart (state : S)

abbrev Event (Q : Type*) := Q × Option Bool

/-- Reachability in the persistent service. A missing bit records an actual restart. -/
inductive ServicePath (serve : S → Q → Reply S) : S → List (Event Q) → S → Prop where
  | nil (s) : ServicePath serve s [] s
  | answer {s s' t q b log} : serve s q = .answer b s' → ServicePath serve s' log t →
      ServicePath serve s ((q, some b) :: log) t
  | restart {s s' t q log} : serve s q = .restart s' → ServicePath serve s' log t →
      ServicePath serve s ((q, none) :: log) t

theorem ServicePath.append {serve : S → Q → Reply S} {s t u : S} {log more : List (Event Q)}
    (a : ServicePath serve s log t) (b : ServicePath serve t more u) :
    ServicePath serve s (log ++ more) u := by
  induction a with
  | nil => exact b
  | answer h _ ih => exact .answer h (ih b)
  | restart h _ ih => exact .restart h (ih b)

/-- A completed run of the ordinary sign learner. -/
inductive LearnerRun (step : P → Move P Q O) : P → List (Event Q) → O → Prop where
  | done {p x} : step p = .done x → LearnerRun step p [] x
  | work {p p' log x} : step p = .work p' → LearnerRun step p' log x → LearnerRun step p log x
  | query {p q no yes log x} (b : Bool) : step p = .query q no yes →
      LearnerRun step (if b then yes else no) log x → LearnerRun step p ((q, some b) :: log) x

/-- All possible answer streams, including inconsistent ones, halt within the stated fuel. -/
def Bounded (step : P → Move P Q O) : ℕ → P → Prop
  | 0, _ => False
  | h + 1, p => match step p with
    | .done _ => True
    | .work p' => Bounded step h p'
    | .query _ no yes => Bounded step h no ∧ Bounded step h yes

inductive End (O : Type*) where
  | done (x : O)
  | restart
  | expired

structure Epoch (S Q O : Type*) where
  outcome : End O
  state : S
  log : List (Event Q)
  learnerSteps : ℕ

/-- Run until halt, the first restart, or the supplied fuel limit. The log witnesses the
previous queries for the proof; the learner and service cannot inspect it through this API. -/
def runEpoch (step : P → Move P Q O) (serve : S → Q → Reply S) : ℕ → P → S → Epoch S Q O
  | 0, _, s => ⟨.expired, s, [], 0⟩
  | h + 1, p, s => match step p with
    | .done x => ⟨.done x, s, [], 1⟩
    | .work p' =>
      let r := runEpoch step serve h p' s
      { r with learnerSteps := r.learnerSteps + 1 }
    | .query q no yes => match serve s q with
      | .restart s' => ⟨.restart, s', [(q, none)], 1⟩
      | .answer b s' =>
        let r := runEpoch step serve h (if b then yes else no) s'
        { r with log := (q, some b) :: r.log, learnerSteps := r.learnerSteps + 1 }

def restartCount (log : List (Event Q)) : ℕ := (log.filter (fun e => e.2.isNone)).length

@[simp] theorem restartCount_nil : restartCount ([] : List (Event Q)) = 0 := rfl

@[simp] theorem restartCount_answer (q : Q) (b : Bool) (log : List (Event Q)) :
    restartCount ((q, some b) :: log) = restartCount log := by simp [restartCount]

@[simp] theorem restartCount_restart (q : Q) (log : List (Event Q)) :
    restartCount ((q, none) :: log) = restartCount log + 1 := by simp [restartCount]

@[simp] theorem restartCount_append (a b : List (Event Q)) :
    restartCount (a ++ b) = restartCount a + restartCount b := by simp [restartCount]

/-- Every single-epoch log is a realizable sequence of service transitions. Its length counts
all requests, including the request causing a restart. A completed epoch has an ordinary
learner transcript, and an interrupted epoch contains precisely one restart. -/
theorem runEpoch_spec (step : P → Move P Q O) (serve : S → Q → Reply S) (h : ℕ) (p : P) (s : S)
    (hb : Bounded step h p) :
    let r := runEpoch step serve h p s
    ServicePath serve s r.log r.state ∧ r.log.length ≤ h ∧
      match r.outcome with
      | .done x => LearnerRun step p r.log x ∧ restartCount r.log = 0
      | .restart => restartCount r.log = 1
      | .expired => False := by
  induction h generalizing p s with
  | zero => exact False.elim hb
  | succ h ih =>
    cases hx : step p with
    | done x => simp [runEpoch, hx, ServicePath.nil, LearnerRun.done hx]
    | work p' =>
      obtain ⟨path,len,finish⟩ := ih p' s (by simpa [Bounded,hx] using hb)
      simp only [runEpoch,hx]
      refine ⟨path, len.trans (Nat.le_succ _), ?_⟩
      cases hz : (runEpoch step serve h p' s).outcome <;> simp only [hz] at finish ⊢
      · exact ⟨.work hx finish.1, finish.2⟩
      · exact finish
    | query q no yes =>
      cases hr : serve s q with
      | restart s' =>
        simp only [runEpoch,hx,hr,List.length_cons,List.length_nil,restartCount_restart,
          restartCount_nil,zero_add,and_true]
        exact ⟨.restart hr (.nil _), by omega⟩
      | answer b s' =>
        have hby : Bounded step h no ∧ Bounded step h yes := by simpa [Bounded,hx] using hb
        have hbc : Bounded step h (if b then yes else no) := by cases b <;> simp_all
        obtain ⟨path,len,finish⟩ := ih _ s' hbc
        simp only [runEpoch,hx,hr,List.length_cons,restartCount_answer]
        refine ⟨.answer hr path, Nat.succ_le_succ len, ?_⟩
        cases hz : (runEpoch step serve h (if b then yes else no) s').outcome <;>
          simp only [hz] at finish ⊢
        · exact ⟨.query b hx finish.1, finish.2⟩
        · exact finish

structure RunResult (S Q O : Type*) where
  value : Option O
  state : S
  log : List (Event Q)
  learnerSteps : ℕ

/-- A budget of `attempts` epochs. On a restart only the learner state is reset. -/
def run (step : P → Move P Q O) (serve : S → Q → Reply S) (h : ℕ) (p : P) :
    ℕ → S → RunResult S Q O
  | 0, s => ⟨none, s, [], 0⟩
  | n + 1, s =>
    let r := runEpoch step serve h p s
    match r.outcome with
    | .done x => ⟨some x, r.state, r.log, r.learnerSteps⟩
    | .expired => ⟨none, r.state, r.log, r.learnerSteps⟩
    | .restart =>
      let rest := run step serve h p n r.state
      ⟨rest.value, rest.state, r.log ++ rest.log, r.learnerSteps + rest.learnerSteps⟩

/-- Each completed epoch has one common witness for all its answered requests. The witness
may be different after a restart, while every witness forces the same winning output. -/
theorem run_spec (step : P → Move P Q O) (serve : S → Q → Reply S) (h : ℕ) (p : P)
    (initial : S) (winning : O) (valid : W → Q → Bool → Prop) (hb : Bounded step h p)
    (common : ∀ {s t} (past log : List (Event Q)), ServicePath serve initial past s →
      ServicePath serve s log t → restartCount log = 0 →
      ∃ w : W, ∀ q b, (q, some b) ∈ log → valid w q b)
    (sound : ∀ {log x}, LearnerRun step p log x →
      (∃ w : W, ∀ q b, (q, some b) ∈ log → valid w q b) → x = winning)
    (attempts : ℕ) : ∀ {s} (past : List (Event Q)), ServicePath serve initial past s →
    let r := run step serve h p attempts s
    ServicePath serve s r.log r.state ∧ r.log.length ≤ attempts * h ∧
      match r.value with
      | some x => x = winning
      | none => attempts ≤ restartCount r.log := by
  induction attempts with
  | zero => intro s past _; simp [run, ServicePath.nil]
  | succ n ih =>
    intro s past reach
    obtain ⟨path,len,finish⟩ := runEpoch_spec step serve h p s hb
    cases hz : (runEpoch step serve h p s).outcome with
    | expired => simp only [hz] at finish
    | done x =>
      simp only [hz] at finish
      simp only [run,hz]
      refine ⟨path, ?_, sound finish.1 (common past _ reach path finish.2)⟩
      rw [Nat.succ_mul]; omega
    | restart =>
      simp only [hz] at finish
      obtain ⟨endPath,total,correct⟩ := ih (past ++ _) (reach.append path)
      simp only [run,hz,List.length_append]
      refine ⟨path.append endPath, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · cases hout : (run step serve h p n (runEpoch step serve h p s).state).value <;>
          simp only [hout,restartCount_append,finish] at correct ⊢
        · omega
        · exact correct

/-- Section 2 wrapper. A cap of `restarts` on service restarts and `h` steps on any sign
learner transcript gives the correct sign in at most `(restarts + 1) * h` service requests. -/
theorem restart_recovery (step : P → Move P Q O) (serve : S → Q → Reply S) (h restarts : ℕ)
    (p : P) (initial : S) (winning : O) (valid : W → Q → Bool → Prop) (hb : Bounded step h p)
    (common : ∀ {s t} (past log : List (Event Q)), ServicePath serve initial past s →
      ServicePath serve s log t → restartCount log = 0 →
      ∃ w : W, ∀ q b, (q, some b) ∈ log → valid w q b)
    (sound : ∀ {log x}, LearnerRun step p log x →
      (∃ w : W, ∀ q b, (q, some b) ∈ log → valid w q b) → x = winning)
    (cap : ∀ {t} (log : List (Event Q)), ServicePath serve initial log t → restartCount log ≤ restarts) :
    let r := run step serve h p (restarts + 1) initial
    r.value = some winning ∧ r.log.length ≤ (restarts + 1) * h := by
  obtain ⟨path,len,correct⟩ := run_spec step serve h p initial winning valid hb common sound
    (restarts + 1) [] (.nil initial)
  refine ⟨?_, len⟩
  cases hz : (run step serve h p (restarts + 1) initial).value with
  | none =>
    simp only [hz] at correct
    have := cap _ path
    omega
  | some x => simpa only [hz, Option.some.injEq] using correct

/-- Count all ordinary learner moves as well as service requests. This bound is unconditional,
even when every label is inconsistent or the service restarts at every opportunity. -/
theorem epoch_step_counts (step : P → Move P Q O) (serve : S → Q → Reply S)
    (h : ℕ) (p : P) (s : S) :
    let r := runEpoch step serve h p s
    r.log.length ≤ r.learnerSteps ∧ r.learnerSteps ≤ h := by
  induction h generalizing p s with
  | zero => simp [runEpoch]
  | succ h ih =>
    cases hx : step p with
    | done x => simp [runEpoch,hx]
    | work p' =>
      obtain ⟨a,b⟩ := ih p' s
      simp only [runEpoch,hx]
      omega
    | query q no yes =>
      cases hr : serve s q with
      | restart s' => simp [runEpoch,hx,hr]
      | answer b s' =>
        obtain ⟨a,c⟩ := ih (if b then yes else no) s'
        simp only [runEpoch,hx,hr,List.length_cons]
        omega

theorem total_step_counts (step : P → Move P Q O) (serve : S → Q → Reply S)
    (h : ℕ) (p : P) (tries : ℕ) (s : S) :
    let r := run step serve h p tries s
    r.log.length ≤ r.learnerSteps ∧ r.learnerSteps ≤ tries * h := by
  induction tries generalizing s with
  | zero => simp [run]
  | succ n ih =>
    obtain ⟨a,b⟩ := epoch_step_counts step serve h p s
    obtain ⟨c,d⟩ := ih (runEpoch step serve h p s).state
    cases hz : (runEpoch step serve h p s).outcome <;>
      simp only [run,hz,List.length_append,Nat.succ_mul] <;> omega

/-- Native learner work plus an upper bound on the cost of the calls actually issued. -/
theorem combined_step_bound (step : P → Move P Q O) (serve : S → Q → Reply S)
    (h restarts perRequest : ℕ) (p : P) (s : S) :
    let r := run step serve h p (restarts + 1) s
    r.learnerSteps + r.log.length * perRequest ≤ (restarts + 1) * h * (1 + perRequest) := by
  obtain ⟨a,b⟩ := total_step_counts step serve h p (restarts+1) s
  simp only [Nat.mul_add, Nat.mul_one]
  exact Nat.add_le_add b (Nat.mul_le_mul_right perRequest (a.trans b))

end Recovery
end LinearProgramming
end Optimization
end OAI
