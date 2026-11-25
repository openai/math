import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace OAI
/-! # Sparse exact corrections for products of approximations

The complement of the retained tensor expansion consists precisely of the
subsets with more than the allowed number of errors. The binomial estimate
below uses a single scalar weight for every selected error.
-/

namespace Hierarchy.SparseCorrection

open scoped BigOperators Classical
open Finset

def term {R : Type*} [CommMonoid R] {s : ℕ} (error ordinary : Fin s → R)
    (J : Finset (Fin s)) : R :=
  (∏ i ∈ J, error i) * ∏ i ∈ Jᶜ, ordinary i

/-- Exact partition of the powered ideal tensor, also valid pointwise over any field. -/
theorem split {R : Type*} [CommRing R] {s : ℕ} (ideal ordinary : Fin s → R) (p : ℕ) :
    (∏ i, ideal i) -
      ∑ J ∈ univ.filter (fun J : Finset (Fin s) => J.card ≤ p),
        term (ideal - ordinary) ordinary J =
      ∑ J ∈ univ.filter (fun J : Finset (Fin s) => p < J.card),
        term (ideal - ordinary) ordinary J := by
  apply sub_eq_iff_eq_add.mpr
  rw [add_comm]
  have h := Fintype.prod_add (fun j => ideal j - ordinary j) ordinary
  simpa only [sub_add_cancel, term, Pi.sub_apply, not_le] using
    h.trans (sum_filter_add_sum_filter_not univ (fun J : Finset (Fin s) => J.card ≤ p)
      (term (ideal - ordinary) ordinary)).symm

/-- Upper bound for the normalized spectral values of all discarded terms. -/
theorem omitted_le (s p : ℕ) {h z : ℝ} (hh : 0 < h) (hz : 0 ≤ z) (hsmall : h*z ≤ 1) :
    (∑ J ∈ univ.filter (fun J : Finset (Fin s) => p < J.card),
      z ^ J.card * (1+z) ^ Jᶜ.card) ≤ (h*z)^(p+1) * (1+z+1/h)^s := by
  let A := univ.filter (fun J : Finset (Fin s) => p < J.card)
  have weight (J : Finset (Fin s)) (hJ : J ∈ A) :
      z^J.card * (1+z)^Jᶜ.card ≤
        (h*z)^(p+1) * ((1/h)^J.card * (1+z)^Jᶜ.card) := by
    have hcard : p+1 ≤ J.card := (mem_filter.mp hJ).2
    have hp := pow_le_pow_of_le_one (mul_nonneg hh.le hz) hsmall hcard
    have hfac : (h*z) * (1/h) = z := by field_simp
    calc
      z^J.card * (1+z)^Jᶜ.card =
          (h*z)^J.card * ((1/h)^J.card * (1+z)^Jᶜ.card) := by
            rw [← mul_assoc, ← mul_pow, hfac]
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)
  calc
    _ ≤ ∑ J ∈ A, (h*z)^(p+1) * ((1/h)^J.card * (1+z)^Jᶜ.card) :=
      sum_le_sum weight
    _ ≤ ∑ J : Finset (Fin s), (h*z)^(p+1) * ((1/h)^J.card * (1+z)^Jᶜ.card) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
    _ = _ := by
      rw [← mul_sum]
      congr 1
      simpa only [prod_const, card_univ, Fintype.card_fin, add_comm (1/h)] using
        (Fintype.prod_add (fun _ : Fin s => 1/h) (fun _ => 1+z)).symm

private theorem logb_overhead {h z : ℝ} (hh : 0 < h) (hz : 0 ≤ z) (hu : z ≤ 1/h) :
    Real.logb 2 (1+z+1/h) ≤ 3/h := by
  have hx : 0 < 1 + z + 1/h := by positivity
  have hlog : Real.log (1+z+1/h) ≤ 2/h := by
    calc
      _ ≤ (1+z+1/h)-1 := Real.log_le_sub_one_of_pos hx
      _ ≤ (1+1/h+1/h)-1 := by linarith
      _ = 2/h := by ring
  rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))]
  apply hlog.trans
  have hc : (2:ℝ) ≤ 3 * Real.log 2 := by linarith [Real.log_two_gt_d9]
  calc 2/h ≤ (3 * Real.log 2)/h := by gcongr
       _ = _ := by ring

/-- The logarithmic loss of the binomial sum leaves at least half of the
per-selected-copy price discount when the amplification threshold holds. -/
theorem price_discount {h c D z : ℝ} {s p : ℕ}
    (hh : 0 < h) (hc : 0 < c) (hz : 0 < z) (hsmall : z ≤ 1/h)
    (normalized : c * Real.logb 2 z = -D)
    (threshold : 2*c*(Real.logb 2 h+3) ≤ D)
    (copies : (s : ℝ)/h ≤ p+1) :
    c * Real.logb 2 ((h*z)^(p+1) * (1+z+1/h)^s) ≤ -((s:ℝ)*D/(2*h)) := by
  have gover := logb_overhead hh hz.le hsmall
  have hneg : c*Real.logb 2 h - D ≤ 0 := by
    have hm : h*z ≤ 1 := by simpa only [mul_comm] using (le_div_iff₀ hh).mp hsmall
    have hv := Real.logb_nonpos (by norm_num : (1:ℝ)<2) (mul_pos hh hz).le hm
    rw [Real.logb_mul hh.ne' hz.ne'] at hv
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc.le hv]
  have hj := mul_le_mul_of_nonpos_right copies hneg
  have hk := mul_le_mul_of_nonneg_left gover (mul_nonneg hc.le (Nat.cast_nonneg s))
  have hbudget := mul_le_mul_of_nonneg_left threshold (div_nonneg (Nat.cast_nonneg s) hh.le)
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
    Real.logb_mul hh.ne' hz.ne', Nat.cast_add, Nat.cast_one]
  have hs : (s:ℝ) * D / (2*h) = ((s:ℝ)/h)*D/2 := by ring
  rw [hs]
  have ho : (c*(s:ℝ))*(3/h) = ((s:ℝ)/h)*(3*c) := by ring
  rw [ho] at hk
  nlinarith [show ((p:ℝ)+1)*(c*Real.logb 2 z) = ((p:ℝ)+1)*(-D) by rw [normalized]]

end Hierarchy.SparseCorrection

end OAI
