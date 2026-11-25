import OAI.Computability.NearSquareRoot.PrecisionPlacedSlot
import OAI.Computability.NearSquareRoot.SynchronizedScheduleSemantics

/-! # Reading scalar actions from physical synchronized instruction rows -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Strip Staff SynchronizedLayers.ScheduleProgram

variable {I X : Type} [Codec X] {s : Regime I} {bits : I → ℕ}

/-- A synchronized block with no instruction acts by a unit coefficient.
The construction reads the encoded option and runs the corresponding scalar
evaluation for any payload actually supplied by the stage. -/
theorem Prepared.optional (P : Realizes s bits) (default : X) {op : I → Option X} (O : s.Has op)
    (f : I → X → ℂ)
    (phase : ∀ (v : I → X), s.Has v → Prepared s bits (fun j ↦ f j (v j))) :
    Prepared s bits (fun j ↦ (op j).elim 1 (f j)) := by
  have flag : s.Has (fun j ↦ (op j).isSome) := by
    have found := O.ez (easyOption false (fun _ : X ↦ true) (Easy.const _))
    convert found using 2
    rename_i j
    cases op j <;> rfl
  have operand := O.ez (easyOption default id Easy.identity)
  have result := Prepared.branch flag (phase _ operand) (Prepared.one P)
  convert result using 2
  rename_i j
  cases op j <;> rfl

omit [Codec X] in
private theorem headD_drop (d : X) (l : List X) (n : ℕ) : (l.drop n).headD d = l[n]?.getD d := by
  simp

/-- Select a row by its unary schedule address, including its orientation bit. -/
theorem headerElement {Y : Type} [Codec Y] {v : I → List Y} {index : I → ℕ} (d : Y)
    (H : s.Has v) (T : Realizes s index) :
    s.Has (fun j ↦ (v j)[index j]?.getD d) := by
  have result := (Regime.Has.pair H T).ez (Iter.facile d)
  simpa only [Iter.pick, Function.comp_def, box, tally_length, headD_drop] using result

/-- Read the selected block field of one synchronized row. Rows too short to
contain that block supply the same idle code as an explicit absent action. -/
theorem readBlockAvailable {r : I → Row X} {b : I → ℕ} (R : s.Has r) (B : Realizes s b) :
    s.Has (fun j ↦ readBlock (r j) (b j)) := by
  have result := headerElement (none : Option X) (R.ez Easy.snd) B
  convert result using 2
  rename_i j
  unfold readBlock
  cases (r j).2[b j]? <;> rfl

/-- The phase query produced at an address in a directed schedule. -/
def directedQuery (plan : List (Bool × Row X)) (stage block : ℕ) : Bool × Option X :=
  let row := plan[stage]?.getD (false, (false,false), [])
  (row.1, readBlock row.2 block)

/-- Both the selected action and the orientation can be supplied to local
phase setup by scanning the very schedule that is executed. -/
theorem directedQueryAvailable {plan : I → List (Bool × Row X)} {stage block : I → ℕ}
    (H : s.Has plan) (T : Realizes s stage) (B : Realizes s block) :
    s.Has (fun j ↦ directedQuery (plan j) (stage j) (block j)) := by
  have row := headerElement (false, (false,false), []) H T
  exact (row.ez Easy.fst).pair (readBlockAvailable (row.ez Easy.snd) B)

/-- The global orientation on the schedule conjugates the chosen local
coefficient; empty block fields and missing rows are identity phases. -/
theorem prepareDirectedQuery {plan : I → List (Bool × Row X)} {stage block : I → ℕ}
    (P : Realizes s bits) (d : X) (H : s.Has plan) (T : Realizes s stage) (B : Realizes s block)
    (f : I → X → ℂ)
    (phase : ∀ (v : I → X), s.Has v → Prepared s bits (fun j ↦ f j (v j))) :
    Prepared s bits (fun j ↦
      let query := directedQuery (plan j) (stage j) (block j)
      adjointValue query.1 (query.2.elim 1 (f j))) := by
  have result := directedQueryAvailable H T B
  exact Prepared.adjoint (result.ez Easy.fst) (Prepared.optional P d (result.ez Easy.snd) f phase)

end PhaseTable

end NearSquareRoot
end Computability
end OAI
