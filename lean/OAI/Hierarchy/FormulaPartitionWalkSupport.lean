import OAI.Hierarchy.FormulaPartitionWalkFactors
import OAI.Hierarchy.FormulaPartitionCount

namespace OAI
/-! # Restricting marked-walk sums to the admissible halving partitions -/

namespace Hierarchy.FormulaPartition

open scoped Classical BigOperators
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {τ : V → Type} {F : Type*} [Field F]
local notation "d" => Fintype.card V
local notation "t" => Nat.log 2 d

/-- The same factors give the complete walk and vanish termwise outside the
family of admissible partitions. -/
theorem run_partition_factors_support (ks : List (Kernel V τ F)) (tip : Leaf V τ F)
    (large : 2≤d) :
    ∃ fac : FormulaPartitionRank.Partition V (t+1) → Positions t ks.length →
        Fin (t+1) → ((v : V) → τ v) → F,
      (∀ π pos j, FormulaPartitionRank.Depends π j (fac π pos j)) ∧
      (∀ a, run a tip ks Finset.univ = ∑ π, ∑ pos, ∏ j, fac π pos j a) ∧
      (∀ π, π ∉ admissiblePartitions V t → ∀ pos a, (∏ j,fac π pos j a) = 0) := by
  choose fac localFac eqFac using markedWeight_factors ks tip
  refine ⟨fac,localFac,?_,?_⟩
  · intro a
    rw [run_eq_sum_markedWeight ks tip a (by omega)]
    exact Finset.sum_congr rfl fun π _ =>
      Finset.sum_congr rfl fun pos _ => eqFac π pos a
  · intro π ignored pos a
    have oversized : ¬ (∀ j : Fin (t+1), (colorTail π j).card ≤ threshold d j.val) :=
      fun h => ignored (by
        simpa only [admissiblePartitions, Finset.mem_filter, Finset.mem_univ, true_and] using h)
    obtain ⟨j,hj⟩ := not_forall.mp oversized
    rw [← eqFac π pos a]
    exact markedWeight_eq_zero_of_tail ks tip pos a j (lt_of_not_ge hj)

end
end Hierarchy.FormulaPartition

end OAI
