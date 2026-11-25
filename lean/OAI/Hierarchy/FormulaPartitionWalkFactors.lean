import OAI.Hierarchy.FormulaPartitionMarkedFactors

namespace OAI
/-! # Grouped tensor factors of a single balanced formula walk -/

namespace Hierarchy.FormulaPartition

open scoped Classical BigOperators
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {τ : V → Type} {F : Type*} [Field F]
local notation "d" => Fintype.card V
local notation "t" => Nat.log 2 d

/-- Each pair of a slot coloring and a mask of marked gates contributes a pure
tensor across the color blocks. There are at most two choices per gate for the mask. -/
theorem run_partition_factors (ks : List (Kernel V τ F)) (tip : Leaf V τ F) (large : 2≤d) :
    ∃ fac : FormulaPartitionRank.Partition V (t+1) → Positions t ks.length →
        Fin (t+1) → ((v : V) → τ v) → F,
      (∀ π pos j, FormulaPartitionRank.Depends π j (fac π pos j)) ∧
      ∀ a, run a tip ks Finset.univ = ∑ π, ∑ pos, ∏ j, fac π pos j a := by
  choose fac localFac eqFac using markedWeight_factors ks tip
  refine ⟨fac,localFac,?_⟩
  intro a
  rw [run_eq_sum_markedWeight ks tip a (by omega)]
  exact Finset.sum_congr rfl fun π _ =>
    Finset.sum_congr rfl fun pos _ => eqFac π pos a

end
end Hierarchy.FormulaPartition

end OAI
