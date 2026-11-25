import OAI.Hierarchy.FormulaPartitionAssembly
import OAI.Hierarchy.FormulaPartitionWalkSupport

namespace OAI
/-! # Grouped coefficient rank of an arbitrary commutative formula -/

namespace Hierarchy.FormulaPartition
open ABPFirstCut FormulaPartitionRank
open scoped BigOperators Classical
noncomputable section

variable {V : Type} [Fintype V] {τ : V → Type} {F : Type*} [Field F]

private theorem factors_supported {s : ℕ} {p : MvPolynomial (Σ v,τ v) F}
    (size : HasFormula s p) (d : 2 ≤ Fintype.card V) :
    ∃ g : (π : Partition V (Nat.log 2 (Fintype.card V)+1)) → Fin ((s+2)^24) →
        (j : Fin (Nat.log 2 (Fintype.card V)+1)) → Fiber τ π j → F,
      (∀ a, slotCoeff a Finset.univ p = ∑ π, ∑ r, ∏ j, g π r j (restrict π j a)) ∧
      ∀ π, π ∉ admissiblePartitions V (Nat.log 2 (Fintype.card V)) →
        ∀ a, (∑ r, ∏ j, g π r j (restrict π j a)) = 0 :=
  assemble_route_factors size (fun steps tip => run_partition_factors_support steps tip d)

/-- One tensor of grouped rank at most `(s+2)^24` for each surjective slot coloring. -/
theorem hasFormula_factorization {s : ℕ} {p : MvPolynomial (Σ v,τ v) F}
    (size : HasFormula s p) (d : 2 ≤ Fintype.card V) :
    ∃ g : (π : Partition V (Nat.log 2 (Fintype.card V)+1)) → Fin ((s+2)^24) →
        (j : Fin (Nat.log 2 (Fintype.card V)+1)) → Fiber τ π j → F,
      ∀ a, slotCoeff a Finset.univ p = ∑ π, ∑ r, ∏ j, g π r j (restrict π j a) := by
  obtain ⟨g, full, _⟩ := factors_supported size d
  exact ⟨g,full⟩

/-- The support is a fixed family determined by the slots alone, so it can be
used for every formula in a fixed-size model. -/
theorem hasFormula_admissible_factorization {s : ℕ} {p : MvPolynomial (Σ v,τ v) F}
    (size : HasFormula s p) (large : 2 ≤ Fintype.card V) :
    ∃ g : (π : Partition V (Nat.log 2 (Fintype.card V)+1)) → Fin ((s+2)^24) →
        (j : Fin (Nat.log 2 (Fintype.card V)+1)) → Fiber τ π j → F,
      ∀ a, slotCoeff a Finset.univ p =
        ∑ π ∈ admissiblePartitions V (Nat.log 2 (Fintype.card V)), ∑ r, ∏ j, g π r j (restrict π j a) := by
  classical
  obtain ⟨g,full,outside⟩ := factors_supported size large
  refine ⟨g,fun a => ?_⟩
  rw [full]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun π _ miss => outside π miss a)).symm

/-- Only `2^(2*d)` of the partitions are needed for a tensor with `d` slots. -/
theorem hasFormula_sparse_factorization {s : ℕ} {p : MvPolynomial (Σ v,τ v) F}
    (size : HasFormula s p) (large : 2 ≤ Fintype.card V) :
    ∃ (Ps : Finset (Partition V (Nat.log 2 (Fintype.card V)+1)))
      (g : (π : Partition V (Nat.log 2 (Fintype.card V)+1)) → Fin ((s+2)^24) →
        (j : Fin (Nat.log 2 (Fintype.card V)+1)) → Fiber τ π j → F),
      Ps.card ≤ 2^(2*Fintype.card V) ∧
      ∀ a, slotCoeff a Finset.univ p = ∑ π ∈ Ps, ∑ r, ∏ j, g π r j (restrict π j a) := by
  obtain ⟨g,eqn⟩ := hasFormula_admissible_factorization size large
  exact ⟨_,g,card_admissiblePartitions V _,eqn⟩

end
end Hierarchy.FormulaPartition

end OAI
