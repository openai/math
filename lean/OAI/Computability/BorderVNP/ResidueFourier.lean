import Mathlib.FieldTheory.Finite.Basic
import OAI.Computability.BorderVNP.ResidueBox

/-!
# Coefficient extraction for the residue matrices

The interpolation formula in §10.2 (page 38) reads a coefficient of a Laurent polynomial
using evaluations on the multiplicative grid of a finite extension. Each exponent lies in
a translated coordinate interval. Only its width matters, including in the Laurent
parameter where the translation can be negative.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueFourier

open scoped BigOperators Classical

variable {ι E K : Type*} [Fintype ι] [Field E] [Field K]

/-- Evaluation of one Laurent monomial on a tuple of nonzero field elements. -/
def monomialValue (x : ι → Kˣ) (a : ι → ℤ) : K := ∏ i, (x i : K) ^ (a i)

/-- Evaluation after extending the field of coefficients. Exponents are signed in every
coordinate, so the last coordinate can represent the Laurent parameter. -/
noncomputable def gridValue (φ : E →+* K) (v : (ι → ℤ) →₀ E) (x : ι → Kˣ) : K :=
  ∑ a ∈ v.support, φ (v a) * monomialValue x a

/-- The product of a monomial and an inverse monomial has their exponent difference. -/
theorem monomialValue_mul_neg (x : ι → Kˣ) (a j : ι → ℤ) :
    monomialValue x a * monomialValue x (-j) = monomialValue x (a - j) := by
  unfold monomialValue
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (zpow_add₀ (x i).ne_zero (a i) (-j i)).symm

variable [Fintype K]

/-- An integer power sums to zero on the nonzero field elements unless its exponent is
divisible by the group order. This includes inverse powers. -/
theorem sum_units_zpow (k : ℤ) :
    ∑ x : Kˣ, (x : K) ^ k =
      if (Fintype.card Kˣ : ℤ) ∣ k then (Fintype.card Kˣ : K) else 0 := by
  classical
  let χ : Kˣ →* K :=
    { toFun := fun x => (x : K) ^ k
      map_one' := by simp
      map_mul' := by intro x y; simp [mul_zpow] }
  have trivial : χ = 1 ↔ (Fintype.card Kˣ : ℤ) ∣ k := by
    constructor
    · intro h
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
      have horder : orderOf g = Fintype.card Kˣ :=
        (orderOf_eq_card_of_forall_mem_zpowers hg).trans Nat.card_eq_fintype_card
      rw [← horder, orderOf_dvd_iff_zpow_eq_one]
      apply Units.ext
      rw [Units.val_zpow_eq_zpow_val]
      exact DFunLike.congr_fun h g
    · intro h
      ext x
      have hd : (orderOf x : ℤ) ∣ k :=
        (Int.natCast_dvd_natCast.mpr orderOf_dvd_card).trans h
      simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply,
        ← Units.val_zpow_eq_zpow_val, orderOf_dvd_iff_zpow_eq_one.mp hd, Units.val_one]
  change ∑ x : Kˣ, χ x = _
  rw [sum_hom_units, trivial]
  split_ifs <;> simp

/-- Character orthogonality on the product grid. -/
theorem sum_monomialValue (a : ι → ℤ) :
    ∑ x : ι → Kˣ, monomialValue x a =
      if ∀ i, (Fintype.card Kˣ : ℤ) ∣ a i
      then (Fintype.card Kˣ : K) ^ Fintype.card ι else 0 := by
  classical
  change (∑ x : ι → Kˣ, ∏ i, (x i : K) ^ (a i)) = _
  rw [← Fintype.prod_sum (fun (i : ι) (u : Kˣ) => (u : K) ^ a i)]
  simp_rw [sum_units_zpow]
  split_ifs with h
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The order of the multiplicative grid is invertible in its field, including in
characteristic two. -/
theorem card_units_ne_zero : (Fintype.card Kˣ : K) ≠ 0 := by
  have h : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [Fintype.card_units, Nat.cast_sub h, FiniteField.cast_card_eq_zero, Nat.cast_one,
    zero_sub]
  exact neg_ne_zero.mpr one_ne_zero

/-- Extract a Laurent coefficient from grid values when its exponent is the unique
representative of its residue class in the support. The exponent being queried may
lie outside the support, in which case both sides vanish. -/
theorem coefficient_of_unique_residue (φ : E →+* K) (v : (ι → ℤ) →₀ E) (j : ι → ℤ)
    (unique : ∀ a ∈ v.support, (∀ i, (Fintype.card Kˣ : ℤ) ∣ a i - j i) → a = j) :
    φ (v j) = ((Fintype.card Kˣ : K) ^ Fintype.card ι)⁻¹ *
      ∑ x : ι → Kˣ, gridValue φ v x * monomialValue x (-j) := by
  classical
  let c : K := (Fintype.card Kˣ : K) ^ Fintype.card ι
  have hc : c ≠ 0 := pow_ne_zero _ card_units_ne_zero
  have sum_eq : (∑ x : ι → Kˣ, gridValue φ v x * monomialValue x (-j)) =
      c * φ (v j) := by
    simp only [gridValue, Finset.sum_mul, mul_assoc, monomialValue_mul_neg]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_monomialValue]
    rw [Finset.sum_eq_single j]
    · simp [c, mul_comm]
    · intro a ha hne
      have h : ¬∀ i, (Fintype.card Kˣ : ℤ) ∣ (a - j) i :=
        fun hdiv => hne (unique a ha hdiv)
      simp only [ite_eq_right_iff.mpr (fun h' => (h h').elim), mul_zero]
    · intro hj
      simp [Finsupp.notMem_support_iff.mp hj]
  rw [sum_eq]
  change φ (v j) = c⁻¹ * (c * φ (v j))
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- Page 38's multiplicative interpolation formula for a box of coordinate width less
than the number of nonzero field elements, allowing arbitrary signed translations. -/
theorem coefficient_on_box (φ : E →+* K) (v : (ι → ℤ) →₀ E) (j lo : ι → ℤ) (width : ℕ)
    (hwidth : width < Fintype.card Kˣ)
    (hj : ∀ i, lo i ≤ j i ∧ j i ≤ lo i + width)
    (hv : ∀ a ∈ v.support, ∀ i, lo i ≤ a i ∧ a i ≤ lo i + width) :
    φ (v j) = ((Fintype.card Kˣ : K) ^ Fintype.card ι)⁻¹ *
      ∑ x : ι → Kˣ, gridValue φ v x * monomialValue x (-j) := by
  apply coefficient_of_unique_residue
  intro a ha hdiv
  funext i
  exact ResidueBox.eq_of_modEq_of_mem_interval (by exact_mod_cast hwidth) (hv a ha i) (hj i)
    (Int.modEq_of_dvd (hdiv i)).symm

end ResidueFourier

end BorderVNP
end Computability
end OAI
