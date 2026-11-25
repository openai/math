import OAI.Hierarchy.ABPFirstCutCoeffProduct
import OAI.Hierarchy.ABPFirstCutRank
import OAI.Hierarchy.SlotCoefficientClosure
import Mathlib.Data.Fintype.Powerset

namespace OAI
/-! # Balanced slot factors from a homogeneous gate decomposition

A product contributes to a multilinear coefficient through all assignments of
the slots to the two factors. If one factor is homogeneous in the balanced
degree range, only balanced sets of slots can occur on that side. Each gate
then contributes one outer product to each such cut.
-/

namespace Hierarchy.CircuitSlot

open ABPFirstCut MvPolynomial
open scoped BigOperators Classical
noncomputable section

/-- Slot sets with cardinality in the interval `(d/3, 2d/3]`. -/
def balancedFamily (V : Type) [Fintype V] : Finset (Finset V) :=
  Finset.univ.filter fun U => Fintype.card V < 3 * U.card ∧ 3 * U.card ≤ 2 * Fintype.card V

@[simp] theorem mem_balancedFamily {V : Type} [Fintype V] (U : Finset V) :
    U ∈ balancedFamily V ↔ Fintype.card V < 3 * U.card ∧ 3 * U.card ≤ 2 * Fintype.card V := by
  simp [balancedFamily]

theorem card_balancedFamily_le (V : Type) [Fintype V] :
    (balancedFamily V).card ≤ 2 ^ Fintype.card V := by
  simpa only [Fintype.card_finset] using (balancedFamily V).card_le_univ

variable {V : Type} [Fintype V] [DecidableEq V] {τ : V → Type} {F : Type*} [Field F]

/-- A balanced homogeneous gate expansion yields one tensor per balanced slot
set with at most `m` rank-one products across each cut. -/
theorem cutFactorization_of_products {m : ℕ} (p : MvPolynomial (Σ i, τ i) F)
    (Q P : Fin m → MvPolynomial (Σ i, τ i) F)
    (degrees : ∀ v, ∃ j : ℕ, (P v).IsHomogeneous j ∧ Fintype.card V < 3 * j ∧
        3 * j ≤ 2 * Fintype.card V)
    (expansion : homogeneousComponent (Fintype.card V) p = ∑ v, Q v * P v) :
    CutFactorization (balancedFamily V) m (fun a => slotCoeff a Finset.univ p) := by
  classical
  choose j hom lower upper using degrees
  apply cutFactorization_of_local (balancedFamily V) m _
    (fun U v a => slotCoeff a U.val (P v))
    (fun U v a => slotCoeff a (Finset.univ \ U.val) (Q v))
  · intro U v a b h
    exact slotCoeff_congr U.val h (P v)
  · intro U v a b h
    exact slotCoeff_congr _ (fun i hi => h i (Finset.mem_sdiff.mp hi).2) (Q v)
  · intro a
    let summand (v : Fin m) (U : Finset V) :=
      slotCoeff a U (P v) * slotCoeff a (Finset.univ \ U) (Q v)
    have split (v : Fin m) : slotCoeff a Finset.univ (Q v * P v) =
        ∑ U ∈ balancedFamily V, summand v U := by
      rw [mul_comm (Q v) (P v), slotCoeff_mul]
      symm
      have sub : balancedFamily V ⊆ (Finset.univ : Finset V).powerset := by
        intro U _
        exact Finset.mem_powerset.mpr (Finset.subset_univ U)
      apply Finset.sum_subset sub
      intro U _ hu
      have hdeg : U.card ≠ j v := by
        intro he
        apply hu
        rw [mem_balancedFamily, he]
        exact ⟨lower v, upper v⟩
      change (P v).coeff (slotExponent a U) * _ = 0
      rw [(hom v).coeff_eq_zero (by simpa only [degree_slotExponent] using hdeg), zero_mul]
    calc
      slotCoeff a Finset.univ p = slotCoeff a Finset.univ (homogeneousComponent (Fintype.card V) p) := by
        simp [slotCoeff, coeff_homogeneousComponent, degree_slotExponent]
      _ = ∑ v, slotCoeff a Finset.univ (Q v * P v) := by
        rw [expansion]
        simp only [slotCoeff, coeff_sum]
      _ = ∑ v, ∑ U ∈ balancedFamily V, summand v U := Fintype.sum_congr _ _ split
      _ = _ := by
        rw [Finset.sum_comm]
        exact (Finset.sum_coe_sort (balancedFamily V) (fun U => ∑ v, summand v U)).symm

end
end Hierarchy.CircuitSlot

end OAI
