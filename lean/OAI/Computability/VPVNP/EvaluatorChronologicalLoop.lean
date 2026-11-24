import OAI.Computability.VPVNP.EvaluatorDigitFetch
import OAI.Computability.VPVNP.EvaluatorTallySemantics

/-! # Chronological traversal of the evaluator digit table

For every digit column the finite control invokes the Frobenius routine,
initializes a label counter and scans the labels in order. Both counters live
on stacks, so the same control works at every width and every label count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorChronologicalLoop

open RAMTape EvaluatorRoutine EvaluatorDigitFetch EvaluatorTallyLoop

variable {P : Type} [DecidableEq P]

/-- One column starts with Frobenius, then enumerates the label digits. -/
def column (frobenius cell : FiniteRoutine (Port P)) : FiniteRoutine (Port P) :=
  (frobenius.followedBy (EvaluatorDigitAddress.copyCount .labels .labelsLeft .copyTmp)).followedBy
    (.ofRoutine (tallyLoop .labelsLeft (.addr .labelIndex) cell.body))

/-- The entry consumes one remaining-column mark per column. -/
def traverse (frobenius cell : FiniteRoutine (Port P)) : FiniteRoutine (Port P) :=
  .ofRoutine (tallyLoop .colsLeft (.addr .columnIndex) (column frobenius cell).body)

variable {S : Type*} (data : List Bool) (t Z ℓ : ℕ) (payload : S → Stacks P)

theorem labelBank (j colsLeft : ℕ) :
    TallyBank (Port.labelsLeft : Port P) (.addr .labelIndex)
      (fun i rem x => bank data t Z ℓ i j rem colsLeft (payload x)) := by
  constructor
  · intros; rfl
  · intros; rfl
  · intro i r x; funext p; cases p <;> rfl
  · intro i r x; funext p; cases p with
    | addr k => cases k <;> rfl
    | _ => rfl
  · intro i x; funext p; cases p with
    | addr k => cases k <;> rfl
    | _ => rfl

theorem columnBank :
    TallyBank (Port.colsLeft : Port P) (.addr .columnIndex)
      (fun j rem x => bank data t Z ℓ 0 j 0 rem (payload x)) := by
  constructor
  · intros; rfl
  · intros; rfl
  · intro i r x; funext p; cases p <;> rfl
  · intro i r x; funext p; cases p with
    | addr k => cases k <;> rfl
    | _ => rfl
  · intro i x; funext p; cases p with
    | addr k => cases k <;> rfl
    | _ => rfl

/-- The elementary control allowance for one complete column. -/
def columnBudget (t BF BC : ℕ) := BF + (5*t+2) + (t*(BC+2)+t+2)

/-- The elementary control allowance for the entire digit schedule. -/
def traverseBudget (t Z BF BC : ℕ) := Z*(columnBudget t BF BC+2)+Z+2

/-- Correctness of the column scan for callbacks with the indicated state effects. -/
theorem column_realizes (frobenius cell : FiniteRoutine (Port P)) (j colsLeft BF BC : ℕ)
    (stepF : (S → ℕ) → S → ℕ) (stepC : ℕ → (S → ℕ) → S → ℕ)
    (hF : Realizes frobenius.body
      (fun x => bank data t Z ℓ 0 j 0 colsLeft (payload x))
      (fun x => bank data t Z ℓ 0 j 0 colsLeft (payload x)) BF stepF)
    (hC : ∀ i rem, i+rem < t → Realizes cell.body
      (fun x => bank data t Z ℓ i j rem colsLeft (payload x))
      (fun x => bank data t Z ℓ i j rem colsLeft (payload x)) BC (stepC i)) :
    Realizes (column frobenius cell).body
      (fun x => bank data t Z ℓ 0 j 0 colsLeft (payload x))
      (fun x => bank data t Z ℓ 0 j 0 colsLeft (payload x)) (columnBudget t BF BC)
      (fun f => stepF ((List.range t).foldr stepC f)) := by
  have hcopy : Realizes (EvaluatorDigitAddress.copyCount Port.labels Port.labelsLeft Port.copyTmp).body
      (fun x => bank data t Z ℓ 0 j 0 colsLeft (payload x))
      (fun x => bank data t Z ℓ 0 j t colsLeft (payload x)) (5*t+2) (fun f x => f x) := by
    apply Realizes.of_runs
    intro x
    refine ⟨_, le_rfl, ?_⟩
    let s := bank data t Z ℓ 0 j 0 colsLeft (payload x)
    have hc := EvaluatorDigitAddress.copyCount_runs Port.labels Port.labelsLeft Port.copyTmp
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) s t 0 rfl rfl rfl
    have he : Function.update s Port.labelsLeft (List.replicate (0+t) true) =
        bank data t Z ℓ 0 j t colsLeft (payload x) := by
      funext p; cases p <;> simp [s, bank]
    exact he ▸ hc
  have hloop := loop_realizes Port.labelsLeft (.addr .labelIndex) cell.body _
    (labelBank data t Z ℓ payload j colsLeft) BC stepC 0 t (by simpa using hC)
  simpa only [column, FiniteRoutine.followedBy, FiniteRoutine.ofRoutine,
    columnBudget, Nat.zero_add, List.range_eq_range'] using (hF.followedBy hcopy).followedBy hloop

/-- The complete scan first composes labels within a column, then composes
the columns chronologically. Both per-call bounds are independent of the indices. -/
theorem traverse_realizes (frobenius cell : FiniteRoutine (Port P)) (BF BC : ℕ)
    (stepF : (S → ℕ) → S → ℕ) (stepC : ℕ → ℕ → (S → ℕ) → S → ℕ)
    (hF : ∀ j left, j+left < Z → Realizes frobenius.body
      (fun x => bank data t Z ℓ 0 j 0 left (payload x))
      (fun x => bank data t Z ℓ 0 j 0 left (payload x)) BF stepF)
    (hC : ∀ j left, j+left < Z → ∀ i rem, i+rem < t → Realizes cell.body
      (fun x => bank data t Z ℓ i j rem left (payload x))
      (fun x => bank data t Z ℓ i j rem left (payload x)) BC (stepC j i)) :
    Realizes (traverse frobenius cell).body
      (fun x => bank data t Z ℓ 0 0 0 Z (payload x))
      (fun x => bank data t Z ℓ 0 0 0 0 (payload x)) (traverseBudget t Z BF BC)
      (fun f => (List.range Z).foldr
        (fun j g => stepF ((List.range t).foldr (stepC j) g)) f) := by
  have hloop := loop_realizes Port.colsLeft (.addr .columnIndex) (column frobenius cell).body _
    (columnBank data t Z ℓ payload) (columnBudget t BF BC)
    (fun j g => stepF ((List.range t).foldr (stepC j) g)) 0 Z (by
      intro j left h
      exact column_realizes data t Z ℓ payload frobenius cell j left BF BC stepF (stepC j)
        (hF _ _ (by omega)) (hC _ _ (by omega)))
  simpa only [traverse, FiniteRoutine.ofRoutine, traverseBudget, Nat.zero_add,
    List.range_eq_range'] using hloop

end EvaluatorChronologicalLoop

end VPVNP
end Computability
end OAI
