import OAI.Computability.BorderVNP.CrossingSignedModes

/-!
# Signed paths for the dual fermion field

Appendix A replaces the factor indexed by `m` with the signed Pascal combination of all
orders at most `m`. This is the exterior action of the Pascal involution defining the
integral dual state. Evaluating its normally ordered creation factors on the vacuum gives
a finite path expansion with at most `L` choices and quadratic bit length per path weight.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Signed

open Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity
open scoped BigOperators

/-- The ordered list of signed Pascal creation factors for the selected state. -/
def dualWord {L : ℕ} (A : Index L) : List ((Fin L → ℤ) × (Fin L → ℤ)) :=
  A.val.sort.map fun m => (fun k => pascalCoefficient m k, fun _ => 0)

private theorem finite_pascal {L m : ℕ} (hm : m < L) :
    finiteVector ℤ L (fun k => pascalCoefficient m k) = Fock.pascal ℤ (Finsupp.single m 1) := by
  ext j
  by_cases hj : j < L
  · exact (finiteVector_apply ℤ L _ ⟨j, hj⟩).trans (Fock.pascal_single_apply ℤ m j).symm
  · rw [Fock.pascal_single_eq_zero_of_lt ℤ (by omega)]
    simp only [finiteVector, Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (show (i : ℕ) ≠ j by have := i.isLt; omega), smul_zero]

private theorem dual_vacuum {L : ℕ} (A : Index L) :
    Fock.pascalExteriorInverse ℤ (Fock.basis ℤ A.val) =
      Fock.normalList ℤ (plainList ℤ L (dualWord A)) (Fock.basis ℤ ∅) := by
  rw [Fock.pascalExteriorInverse_eq, Fock.basis_eq_sorted_prod ℤ A.val, map_list_prod,
    Fock.basis_empty, Fock.normalList_one]
  simp only [dualWord, plainList, List.map_map, Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro m hm
  have hmL := Finset.mem_range.mp ((Finset.mem_powerset.mp A.property) ((Finset.mem_sort _).mp hm))
  rw [finite_pascal hmL]
  exact ExteriorAlgebra.map_apply_ι _ _

/-- The chosen derivative orders, including their exterior permutation signs, compute
exactly the coordinate used by the dual family in the integral crossing. -/
theorem dualState_paths {L : ℕ} (A J : Index L) :
    dualState ℤ L A.val J = ∑ p : ModePath L (dualWord A).length, modeWeight (dualWord A) p J.val ∅ := by
  unfold dualState
  rw [dual_vacuum A, sum_modeWeight]

/-- Each dual path contains at most `L` mode choices. -/
theorem dualWord_length_le {L : ℕ} (A : Index L) : (dualWord A).length ≤ L := by
  simpa [dualWord] using Finset.card_le_card (Finset.mem_powerset.mp A.property)

/-- Each signed multiplicity is representable with `L² + 1` bits. -/
theorem dualWeight_bound {L : ℕ} (A : Index L) (p : ModePath L (dualWord A).length) (J : Index L) :
    (modeWeight (dualWord A) p J.val ∅).natAbs ≤ 2 ^ (L * L) := by
  apply (modeWeight_bound _ L ?_ p J.val ∅).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (dualWord_length_le A)))
  intro a ha k
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ha
  have hmL := Finset.mem_range.mp ((Finset.mem_powerset.mp A.property) ((Finset.mem_sort _).mp hm))
  simp only [pascalCoefficient, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg,
    Int.natAbs_one, one_pow, one_mul, Int.natAbs_natCast, Int.natAbs_zero, Nat.zero_le, and_true]
  exact (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) hmL.le)

end Crossing.Signed

end BorderVNP
end Computability
end OAI
