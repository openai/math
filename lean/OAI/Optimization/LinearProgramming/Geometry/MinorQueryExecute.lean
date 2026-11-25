import OAI.Optimization.LinearProgramming.Geometry.PivotQueries
import OAI.Optimization.LinearProgramming.Geometry.BorderProtocol
import OAI.Optimization.LinearProgramming.Geometry.RecordedHistory

/-! Deterministic replay of an adaptive minor query with a persistent scalar service. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorQuery

open Contract BorderBatch

variable {κ α : Type*}

structure Played (κ α : Type*) where
  answers : List (κ × ℚ)
  out : Sum κ α
  history : Contract.History ℚ

/-- Add a chronological list of accepted replies to a newest-first scalar history. -/
def answeredWords (packet : κ → List ℚ) (xs : List (κ × ℚ)) (old : Contract.History ℚ) : Contract.History ℚ :=
  (xs.map (fun e => (packet e.1,reply (some e.2)))).reverse ++ old

/-- The first restart, when present, is the last exchange in chronologic order. -/
def recorded (packet : κ → List ℚ) (xs : List (κ × ℚ)) (out : Sum κ α) (old : Contract.History ℚ) : Contract.History ℚ :=
  match out with
  | .inl key => (packet key,reply none) :: answeredWords packet xs old
  | .inr _ => answeredWords packet xs old

private theorem recorded_cons (packet : κ → List ℚ) (k : κ) (v : ℚ) (xs : List (κ × ℚ))
    (out : Sum κ α) (old : Contract.History ℚ) :
    recorded packet ((k,v)::xs) out old=recorded packet xs out ((packet k,reply (some v))::old) := by
  cases out <;> simp [recorded,answeredWords,List.append_assoc]

theorem recorded_append (packet : κ → List ℚ) (xs : List (κ × ℚ)) (out : Sum κ α) (old : Contract.History ℚ) :
    recorded packet xs out old=recorded packet xs out [] ++ old := by
  cases out <;> simp [recorded,answeredWords]

/-- Use the actual scalar history before each request to choose the service's next reply. -/
def execute (packet : κ → List ℚ) (ask : Contract.History ℚ → κ → Option ℚ) :
    MinorQuery κ α → Contract.History ℚ → Played κ α
  | .done v, h => ⟨[],.inr v,h⟩
  | .query key next, h =>
    match ask h key with
    | none => ⟨[],.inl key,(packet key,reply none)::h⟩
    | some v =>
      let rest := execute packet ask (next v) ((packet key,reply (some v))::h)
      ⟨(key,v)::rest.answers,rest.out,rest.history⟩

theorem execute_spec (packet : κ → List ℚ) (ask : Contract.History ℚ → κ → Option ℚ)
    (p : MinorQuery κ α) (old : Contract.History ℚ) :
    let z := execute packet ask p old
    Run p z.answers z.out ∧ z.history=recorded packet z.answers z.out old := by
  induction p generalizing old with
  | done v => exact ⟨.done v,rfl⟩
  | query key next ih =>
    cases h : ask old key with
    | none => simp only [execute,h]; exact ⟨.restart key next,rfl⟩
    | some v =>
      simp only [execute,h]
      obtain ⟨required,hist⟩ := ih v ((packet key,reply (some v))::old)
      exact ⟨.answer key next v required,hist.trans (recorded_cons ..).symm⟩

theorem execute_answers (packet : κ → List ℚ) (ask : Contract.History ℚ → κ → Option ℚ)
    (o : ScalarOracle ℚ) (returns : ∀ h k, o h (packet k)=reply (ask h k))
    (p : MinorQuery κ α) (old : Contract.History ℚ) (ok : answersMatch o old) :
    answersMatch o (execute packet ask p old).history := by
  induction p generalizing old with
  | done => exact ok
  | query key next ih =>
    cases h : ask old key with
    | none =>
      simp only [execute,h]
      exact ⟨by simpa only [h] using (returns old key).symm,ok⟩
    | some v =>
      simp only [execute,h]
      exact ih v _ ⟨by simpa only [h] using (returns old key).symm,ok⟩

private theorem cancel_reply {a b : Option ℚ} (eq : reply a=reply b) : a=b := by
  cases a <;> cases b <;> simp_all [reply]

/-- The complete typed outcome and the final history are forced by legality of the
actual replies. The initial scratch memory of a RAM caller does not occur here. -/
theorem execute_of_run (packet : κ → List ℚ) (ask : Contract.History ℚ → κ → Option ℚ)
    (o : ScalarOracle ℚ) (returns : ∀ h k, o h (packet k)=reply (ask h k))
    {p : MinorQuery κ α} {xs out} (run : Run p xs out) (old : Contract.History ℚ)
    (ok : answersMatch o (recorded packet xs out old)) :
    execute packet ask p old=⟨xs,out,recorded packet xs out old⟩ := by
  induction run generalizing old with
  | done v => rfl
  | restart key next =>
    have h : ask old key=none := cancel_reply ((returns old key).symm.trans ok.1.symm)
    simp [execute,h,recorded,answeredWords]
  | @answer key next v xs out tail ih =>
    rw [recorded_cons] at ok ⊢
    have first : answersMatch o ((packet key,reply (some v))::old) := by
      apply answersMatch_suffix o (recorded packet xs out [])
      rw [← recorded_append]
      exact ok
    have h : ask old key=some v := cancel_reply ((returns old key).symm.trans first.1.symm)
    simp only [execute,h,ih _ ok]

end MinorQuery
end Geometry
end LinearProgramming
end Optimization
end OAI
