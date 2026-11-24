import OAI.Computability.VPVNP.EvaluatorChronologicalLoop
import OAI.Computability.VPVNP.EvaluatorTallySafety
import OAI.Computability.VPVNP.EvaluatorDigitRepeat

/-! # Storage and stopping bounds for both evaluator cursors

The table, index tallies, and callback registers account for the storage
between calls. Address lookup and initialization use polynomial scratch
space. The binary digit can trigger many callbacks without increasing the
cursor storage between them.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorChronologicalLoop

open RAMTape EvaluatorDigitFetch EvaluatorTallyLoop EvaluatorRoutineSafety

variable {P S : Type} [DecidableEq P]

/-- Maximum length of a single stack between callbacks. -/
def bankSpace (tableBits t Z ℓ payloadSpace : ℕ) :=
  payloadSpace + tableBits + t + Z + ℓ

/-- A polynomial allowance for addressing, fetching, and both cursor loops. -/
def schedulerSpace (tableBits t Z ℓ payloadSpace : ℕ) :=
  bankSpace tableBits t Z ℓ payloadSpace + (19*(t*Z) + 13*(t*Z*ℓ) + 4) + (5*t+2) + ℓ

variable (data : List Bool) (t Z ℓ space : ℕ) (payload : S → Stacks P)
variable (hp : ∀ x p, (payload x p).length ≤ space)

include hp

omit [DecidableEq P] in
theorem bank_length {i j left cols : ℕ} (hi : i+left ≤ t) (hj : j+cols ≤ Z)
    (x : S) (p : Port P) :
    (bank data t Z ℓ i j left cols (payload x) p).length ≤ bankSpace data.length t Z ℓ space := by
  cases p with
  | addr k =>
    cases k <;> simp only [bank, EvaluatorDigitAddress.ready, Tally.encode,
      EvaluatorDigitAddress.registers, List.length_replicate, bankSpace] <;> omega
  | work p =>
    exact (hp x p).trans (by unfold bankSpace; omega)
  | _ => simp [bank, bankSpace] <;> omega

local notation "cap" => schedulerSpace data.length t Z ℓ space
/-- The storage condition that every named evaluator stack has length at most the given limit. -/
abbrev stackFits {K : Type} (limit : ℕ) (s : Stacks K) : Prop := ∀ p, (s p).length ≤ limit

local notation "fits" => stackFits cap

/-- The unary copy that starts a column and the subsequent label scan respect
the same space bound as the supplied matrix callbacks. -/
theorem column_bounded (frobenius cell : FiniteRoutine (Port P)) (j cols BF BC : ℕ)
    (hj : j+cols ≤ Z)
    (hF : Bounded frobenius.body fits
      (fun x => bank data t Z ℓ 0 j 0 cols (payload x))
      (fun x => bank data t Z ℓ 0 j 0 cols (payload x)) BF)
    (hC : ∀ i left, i+left < t → Bounded cell.body fits
      (fun x => bank data t Z ℓ i j left cols (payload x))
      (fun x => bank data t Z ℓ i j left cols (payload x)) BC) :
    Bounded (column frobenius cell).body fits
      (fun x => bank data t Z ℓ 0 j 0 cols (payload x))
      (fun x => bank data t Z ℓ 0 j 0 cols (payload x)) (columnBudget t BF BC) := by
  have hcopy : Bounded (EvaluatorDigitAddress.copyCount Port.labels Port.labelsLeft Port.copyTmp).body fits
      (fun x => bank data t Z ℓ 0 j 0 cols (payload x))
      (fun x => bank data t Z ℓ 0 j t cols (payload x)) (5*t+2) := by
    apply Bounded.of_runs_with_room (g := id)
    · intro x
      let s := bank data t Z ℓ 0 j 0 cols (payload x)
      have hc := EvaluatorDigitAddress.copyCount_runs Port.labels Port.labelsLeft Port.copyTmp
        (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) s t 0 rfl rfl rfl
      have he : Function.update s Port.labelsLeft (List.replicate (0+t) true) =
          bank data t Z ℓ 0 j t cols (payload x) := by funext p; cases p <;> simp [s, bank]
      exact ⟨_, le_rfl, he ▸ hc⟩
    · intro x u hu p
      have hh := bank_length data t Z ℓ space payload hp (i := 0) (left := 0) (by omega) hj x p
      have h := hu p
      unfold schedulerSpace
      omega
  have hloop := loop_bounded Port.labelsLeft (.addr .labelIndex) cell.body _
    (labelBank data t Z ℓ payload j cols) fits BC 0 t (by
      intro i left hi x p
      have h := bank_length data t Z ℓ space payload hp (by omega : i+left ≤ t) hj x p
      exact h.trans (by unfold schedulerSpace; omega)) (by simpa using hC)
  simpa only [column, FiniteRoutine.followedBy, FiniteRoutine.ofRoutine, columnBudget, Nat.zero_add] using
    (hF.followedBy hcopy).followedBy hloop

/-- Every branch of the complete nested traversal respects the clock and peak
storage, including branches that reject within a matrix query. -/
theorem traverse_bounded (frobenius cell : FiniteRoutine (Port P)) (BF BC : ℕ)
    (hF : ∀ j cols, j+cols < Z → Bounded frobenius.body fits
      (fun x => bank data t Z ℓ 0 j 0 cols (payload x))
      (fun x => bank data t Z ℓ 0 j 0 cols (payload x)) BF)
    (hC : ∀ j cols, j+cols < Z → ∀ i left, i+left < t → Bounded cell.body fits
      (fun x => bank data t Z ℓ i j left cols (payload x))
      (fun x => bank data t Z ℓ i j left cols (payload x)) BC) :
    Bounded (traverse frobenius cell).body fits
      (fun x => bank data t Z ℓ 0 0 0 Z (payload x))
      (fun x => bank data t Z ℓ 0 0 0 0 (payload x)) (traverseBudget t Z BF BC) := by
  have hloop := loop_bounded Port.colsLeft (.addr .columnIndex) (column frobenius cell).body _
    (columnBank data t Z ℓ payload) fits (columnBudget t BF BC) 0 Z (by
      intro j cols hj x p
      have h := bank_length data t Z ℓ space payload hp (i := 0) (left := 0) (by omega)
        (by omega : j+cols ≤ Z) x p
      exact h.trans (by unfold schedulerSpace; omega)) (by
      intro j cols hj
      exact column_bounded data t Z ℓ space payload hp frobenius cell j cols BF BC (by omega)
        (hF _ _ (by omega)) (hC _ _ (by omega)))
  simpa only [traverse, FiniteRoutine.ofRoutine, traverseBudget, Nat.zero_add] using hloop

end EvaluatorChronologicalLoop

end VPVNP
end Computability
end OAI
