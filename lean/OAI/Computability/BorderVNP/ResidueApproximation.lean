import OAI.Computability.BorderVNP.ResidueLaurent
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Laurent-polynomial approximation at the finite branch

Section 10.2 replaces a rational function in the parameters by a polynomial
in the parameters, `t`, and `t⁻¹`, preserving a prescribed residue. We can
clear an arbitrary denominator directly. If `ord(t) = e` and `ord(b) = v`,
then `b^e t^(-v)` has order zero. Its leading coefficient lies in a finite
field, so a fixed positive power has leading coefficient one. A finite
geometric sum now approximates `b⁻¹` to any prescribed precision.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open HahnSeries

variable {κ : Type*} [Field κ]

private theorem order_inv {x : LaurentSeries κ} (hx : x ≠ 0) : x⁻¹.order = -x.order := by
  have h := order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, order_one] at h
  omega

private theorem order_zpow {x : LaurentSeries κ} (hx : x ≠ 0) (n : ℤ) :
    (x ^ n).order = n * x.order := by
  cases n with
  | ofNat n => simp [order_pow]
  | negSucc n => rw [zpow_negSucc, order_inv (pow_ne_zero _ hx), order_pow, Int.negSucc_eq]; simp; ring

private theorem leading_pow (x : LaurentSeries κ) (n : ℕ) :
    (x ^ n).leadingCoeff = x.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, leadingCoeff_mul, ih, pow_succ]

private theorem zpow_mem {S : Subring (LaurentSeries κ)} {t : LaurentSeries κ}
    (ht : t ∈ S) (hti : t⁻¹ ∈ S) (n : ℤ) : t ^ n ∈ S := by
  cases n with
  | ofNat n => exact S.pow_mem ht n
  | negSucc n => rw [zpow_negSucc, ← inv_pow]; exact S.pow_mem hti _

/-- Every nonzero denominator times a Laurent-polynomial multiplier can be
made congruent to one in the residue field. -/
theorem exists_normalized_denominator [Fintype κ] (S : Subring (LaurentSeries κ))
    {t b : LaurentSeries κ} (ht : t ∈ S) (hti : t⁻¹ ∈ S) (hv : 0 < t.order)
    (hb : b ∈ S) (hb0 : b ≠ 0) : ∃ c ∈ S, 0 < (1 - b * c).orderTop := by
  have ht0 : t ≠ 0 := by rintro rfl; simp at hv
  let j := t.order.toNat - 1
  let k := Fintype.card κ - 2
  have hj : (j + 1 : ℕ) = t.order.toNat := by dsimp [j]; omega
  have hk : k + 1 = Fintype.card κ - 1 := by
    dsimp [k]; have := Fintype.one_lt_card (α := κ); omega
  let v := b ^ j * t ^ (-b.order)
  let u := b * v
  have hm : v ∈ S := S.mul_mem (S.pow_mem hb _) (zpow_mem ht hti _)
  have hu : u ∈ S := S.mul_mem hb hm
  have hv0 : v ≠ 0 := mul_ne_zero (pow_ne_zero _ hb0) (zpow_ne_zero _ ht0)
  have hu0 : u ≠ 0 := mul_ne_zero hb0 hv0
  have horder : u.order = 0 := by
    change (b * (b ^ j * t ^ (-b.order))).order = 0
    rw [order_mul hb0 hv0, order_mul (pow_ne_zero _ hb0) (zpow_ne_zero _ ht0), order_pow,
      order_zpow ht0, nsmul_eq_mul]
    have hcast : (j : ℤ) + 1 = t.order := by omega
    rw [← hcast]; ring
  refine ⟨v * u ^ k, S.mul_mem hm (S.pow_mem hu _), ?_⟩
  have he : b * (v * u ^ k) = u ^ (k + 1) := by rw [← mul_assoc, pow_succ']
  rw [he, ← neg_sub, orderTop_neg, orderTop_self_sub_one_pos_iff,
    ← order_eq_orderTop_of_ne_zero (pow_ne_zero _ hu0), order_pow, horder, nsmul_zero,
    leading_pow, hk]
  exact ⟨rfl, FiniteField.pow_card_sub_one_eq_one _ (leadingCoeff_eq_zero.not.mpr hu0)⟩

/-- Approximate a quotient by an element of the Laurent-polynomial ring at
an arbitrary prescribed order, allowing the difference to be exactly zero. -/
theorem approximate_quotient [Fintype κ] (S : Subring (LaurentSeries κ))
    {t a b : LaurentSeries κ} (ht : t ∈ S) (hti : t⁻¹ ∈ S) (hv : 0 < t.order)
    (ha : a ∈ S) (hb : b ∈ S) (N : ℤ) : ∃ f ∈ S, (N : WithTop ℤ) ≤ (a / b - f).orderTop := by
  by_cases hx : a / b = 0
  · exact ⟨0, S.zero_mem, by simp [hx]⟩
  have hb0 : b ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨c, hc, hres⟩ := exists_normalized_denominator S ht hti hv hb hb0
  let d := 1 - b * c
  let n := (N - (a / b).order).toNat + 1
  let G := ∑ i ∈ Finset.range n, d ^ i
  have hd : d ∈ S := S.sub_mem S.one_mem (S.mul_mem hb hc)
  have hg : G ∈ S := S.sum_mem fun i _ => S.pow_mem hd i
  refine ⟨a * c * G, S.mul_mem (S.mul_mem ha hc) hg, ?_⟩
  have hg' : G * (b * c) = 1 - d ^ n := by simpa [G, d] using geom_sum_mul_neg d n
  have he : a / b - a * c * G = a / b * d ^ n := by
    field_simp [hb0]; linear_combination -a * hg'
  rw [he]
  by_cases hd0 : d = 0
  · simp [hd0, n]
  · have hdpos : 0 < d.order := by
      change 0 < d.orderTop at hres
      rwa [← order_eq_orderTop_of_ne_zero hd0, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hres
    rw [← order_eq_orderTop_of_ne_zero (mul_ne_zero hx (pow_ne_zero _ hd0)), WithTop.coe_le_coe,
      order_mul hx (pow_ne_zero _ hd0), order_pow, nsmul_eq_mul]
    have hn : N - (a / b).order ≤ (n : ℤ) := by dsimp [n]; omega
    exact (by nlinarith [(show 0 ≤ (n : ℤ) by positivity),
      mul_nonneg (show 0 ≤ (n : ℤ) by positivity) (show 0 ≤ d.order - 1 by omega)])

/-- Evaluation of the two named Laurent variables, `t` and `t⁻¹`, alongside the
coordinate functions of the chosen branch. -/
noncomputable def branchCoordinates {ι : Type*} (x : ι → LaurentSeries κ) (t : LaurentSeries κ) :
    ι ⊕ Bool → LaurentSeries κ := Sum.elim x (fun b => if b then t else t⁻¹)

/-- Rational functions in the coordinates can be replaced by explicit polynomials
in `x`, `t` and `t⁻¹` without changing their residue against a given differential. -/
theorem exists_residue_polynomial [Fintype κ] {E ι : Type*} [Field E] [Algebra E (LaurentSeries κ)]
    (x : ι → LaurentSeries κ) {t z : LaurentSeries κ} (ht : 0 < t.order)
    (hz : z ∈ IntermediateField.adjoin E (Set.range (branchCoordinates x t))) (η : LaurentSeries κ) :
    ∃ f : MvPolynomial (ι ⊕ Bool) E,
      res (MvPolynomial.aeval (branchCoordinates x t) f * η) = res (z * η) := by
  let y := branchCoordinates x t
  let A := Algebra.adjoin E (Set.range y)
  obtain ⟨a, ha, b, hb, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  have h1 : t ∈ A := Algebra.subset_adjoin ⟨Sum.inr true, rfl⟩
  have h2 : t⁻¹ ∈ A := Algebra.subset_adjoin ⟨Sum.inr false, rfl⟩
  obtain ⟨v, hmem, hv⟩ := approximate_quotient A.toSubring h1 h2 ht ha hb (-η.order)
  obtain ⟨f, hf⟩ : ∃ f : MvPolynomial (ι ⊕ Bool) E, MvPolynomial.aeval y f = v := by
    have hv' : v ∈ (MvPolynomial.aeval (R := E) y).range := by
      rw [MvPolynomial.aeval_range]; exact hmem
    exact hv'
  refine ⟨f, ?_⟩
  change res (MvPolynomial.aeval y f * η) = _
  rw [hf]
  by_cases he : η = 0
  · simp [he]
  by_cases h : a / b - v = 0
  · rw [sub_eq_zero.mp h]
  have hval : -η.order ≤ (a / b - v).order := by
    rwa [← order_eq_orderTop_of_ne_zero h, WithTop.coe_le_coe] at hv
  have hdiff : res ((a / b - v) * η) = 0 :=
    coeff_eq_zero_of_lt_order (by rw [order_mul h he]; omega)
  symm
  simpa only [res, sub_mul, coeff_sub, sub_eq_zero] using hdiff

end Residue

end BorderVNP
end Computability
end OAI
