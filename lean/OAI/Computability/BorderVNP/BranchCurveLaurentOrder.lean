import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Tactic

/-!
# Laurent orders of the bounded eliminant

At a discrete branch with uniformizing variable `s`, the deformation
parameter has order `e > 0`. A nonzero coefficient polynomial in `t` has
order exactly `e` times its trailing degree. Thus a root of a nonzero
bivariate relation with bounded `t`-degree cannot have an arbitrarily
large pole: otherwise the top power of the root is the unique summand of
least order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open HahnSeries

/-- A summand of strictly least order survives a finite sum of Laurent series. -/
theorem order_sum_of_unique_min {κ I : Type*} [Field κ]
    (s : Finset I) (f : I → LaurentSeries κ) (i : I) (hi : i ∈ s) (hn : f i ≠ 0)
    (hmin : ∀ j ∈ s, j ≠ i → (f i).order < (f j).order) :
    ∑ j ∈ s, f j ≠ 0 ∧ (∑ j ∈ s, f j).order = (f i).order := by
  classical
  have hc : (∑ j ∈ s, f j).coeff (f i).order = (f i).coeff (f i).order := by
    rw [coeff_sum]
    exact Finset.sum_eq_single i (fun j hj hji => coeff_eq_zero_of_lt_order (hmin j hj hji))
      (fun h => (h hi).elim)
  have hne := hc.trans_ne (coeff_order_eq_zero.not.mpr hn)
  have h := ne_zero_of_coeff_ne_zero hne
  refine ⟨h, le_antisymm (order_le_of_coeff_ne_zero hne) ((le_order_iff_forall h).mpr ?_)⟩
  intro k hk
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun j hj => coeff_eq_zero_of_lt_order ?_
  obtain rfl | ne := eq_or_ne j i
  · exact hk
  · exact hk.trans (hmin _ hj ne)

/-- Under any field embedding into Laurent series every nonzero element of a
finite constant field has order zero. -/
theorem order_finite_scalar {E κ : Type*} [Field E] [Finite E] [Field κ]
    (φ : E →+* LaurentSeries κ) (a : E) (ha : a ≠ 0) : (φ a).order = 0 := by
  classical
  let := Fintype.ofFinite E
  have eq := FiniteField.pow_card_sub_one_eq_one a ha
  have hn : 0 < Fintype.card E - 1 := by
    have h := Fintype.one_lt_card (α := E)
    omega
  have he := congrArg (fun y : E => (φ y).order) eq
  simp only [map_pow, order_pow, nsmul_eq_mul, map_one, order_one] at he
  exact (mul_eq_zero.mp he).resolve_left (Int.natCast_ne_zero.mpr hn.ne')

/-- The exact order of a nonzero polynomial in the positive-order deformation
parameter. -/
theorem order_eval₂_at_positive_parameter {E κ : Type*} [Field E] [Finite E] [Field κ]
    (φ : E →+* LaurentSeries κ) (τ : LaurentSeries κ) (hτ : 0 < τ.order)
    (p : Polynomial E) (hp : p ≠ 0) :
    p.eval₂ φ τ ≠ 0 ∧ (p.eval₂ φ τ).order = (p.natTrailingDegree : ℤ) * τ.order := by
  have ht : τ ≠ 0 := fun hz => by simp [hz] at hτ
  let f := fun j => φ (p.coeff j) * τ ^ j
  have ho (j) (hj : j ∈ p.support) : (f j).order = (j : ℤ) * τ.order := by
    have hj' := Polynomial.mem_support_iff.mp hj
    simp [f, order_mul ((map_ne_zero_iff _ φ.injective).mpr hj') (pow_ne_zero _ ht),
      order_finite_scalar φ _ hj', order_pow]
  let m := p.natTrailingDegree
  have hm : m ∈ p.support := Polynomial.natTrailingDegree_mem_support_of_nonzero hp
  have hfm : f m ≠ 0 := mul_ne_zero ((map_ne_zero_iff _ φ.injective).mpr
    (Polynomial.mem_support_iff.mp hm)) (pow_ne_zero _ ht)
  have h := order_sum_of_unique_min p.support f m hm hfm (fun j hj hjm => by
    rw [ho _ hm, ho _ hj]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast
      (lt_of_le_of_ne (Polynomial.natTrailingDegree_le_of_mem_supp _ hj) hjm.symm)) hτ)
  rw [Polynomial.eval₂_eq_sum]
  change (∑ j ∈ p.support, f j) ≠ 0 ∧ (∑ j ∈ p.support, f j).order = _
  exact ⟨h.1, h.2.trans (ho _ hm)⟩

/-- The pole of a root of a nonzero bivariate eliminant is bounded by the
parameter ramification index times the maximum coefficient degree in `t`. -/
theorem order_bound_of_eliminant {E κ : Type*} [Field E] [Finite E] [Field κ]
    (φ : E →+* LaurentSeries κ) (τ w : LaurentSeries κ) (hτ : 0 < τ.order)
    (Q : Polynomial (Polynomial E)) (hQ : Q ≠ 0) (D : ℕ)
    (hD : ∀ j ∈ Q.support, (Q.coeff j).natDegree ≤ D)
    (hroot : Q.eval₂ (Polynomial.eval₂RingHom φ τ) w = 0) :
    -(D : ℤ) * τ.order ≤ w.order := by
  by_contra! hw
  have hneg : w.order < 0 := lt_of_lt_of_le hw
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Int.natCast_nonneg D)) hτ.le)
  have hne : w ≠ 0 := fun hz => by simp [hz] at hneg
  let f := fun j => (Q.coeff j).eval₂ φ τ * w ^ j
  let m := Q.natDegree
  have hm : m ∈ Q.support := Polynomial.natDegree_mem_support_of_nonzero hQ
  have he j (hj : j ∈ Q.support) := order_eval₂_at_positive_parameter φ τ hτ (Q.coeff j)
    (Polynomial.mem_support_iff.mp hj)
  have ho j (hj : j ∈ Q.support) : (f j).order =
      ((Q.coeff j).natTrailingDegree : ℤ) * τ.order + j * w.order := by
    rw [show f j = (Q.coeff j).eval₂ φ τ * w ^ j from rfl,
      order_mul (he j hj).1 (pow_ne_zero j hne), (he j hj).2, order_pow, nsmul_eq_mul]
  have hmin j (hj : j ∈ Q.support) (hjm : j ≠ m) : (f m).order < (f j).order := by
    rw [ho _ hm, ho _ hj]
    have hjm' : (j : ℤ) + 1 ≤ m := by exact_mod_cast
      (lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp _ hj) hjm)
    have hd : ((Q.coeff m).natTrailingDegree : ℤ) ≤ D := by
      exact_mod_cast ((Q.coeff m).natTrailingDegree_le_natDegree.trans (hD m hm))
    have h1 := mul_le_mul_of_nonneg_right hd hτ.le
    have h2 := mul_le_mul_of_nonpos_right hjm' hneg.le
    have h3 : 0 ≤ ((Q.coeff j).natTrailingDegree : ℤ) * τ.order := by positivity
    linarith
  apply (order_sum_of_unique_min Q.support f m hm
    (mul_ne_zero (he m hm).1 (pow_ne_zero _ hne)) hmin).1
  rw [Polynomial.eval₂_eq_sum] at hroot
  exact hroot

end Branch

end BorderVNP
end Computability
end OAI
