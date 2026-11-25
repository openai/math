import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Basic.Sign.Basic
import Mathlib.Tactic

/-! The normalized orthogonal residual in the sign-preserving rounding of Appendix A. -/

open scoped BigOperators RealInnerProductSpace
open Submodule WithLp SignType

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

variable {p : ℕ}

/-- Real coordinates of an integer vector. -/
def realCoordinates (a : Fin p → ℤ) : Fin p → ℝ := fun i => a i

/-- The component of `v` orthogonal to the integer directions accumulated so far. -/
noncomputable def residual (S : Submodule ℝ (EuclideanSpace ℝ (Fin p))) (v : Fin p → ℝ) :
    EuclideanSpace ℝ (Fin p) := toLp 2 v - S.starProjection (toLp 2 v)

/-- The residual normalized in the maximum norm on the coordinate functions. -/
noncomputable def roundingDirection (S : Submodule ℝ (EuclideanSpace ℝ (Fin p)))
    (v : Fin p → ℝ) : Fin p → ℝ := fun i => residual S v i / ‖(residual S v).ofLp‖

theorem residual_eq_zero_iff (S : Submodule ℝ (EuclideanSpace ℝ (Fin p))) (v : Fin p → ℝ) :
    residual S v = 0 ↔ toLp 2 v ∈ S := by
  rw [residual, sub_eq_zero, eq_comm, S.starProjection_eq_self_iff]

private theorem infNorm_residual_pos (S : Submodule ℝ (EuclideanSpace ℝ (Fin p))) (v : Fin p → ℝ)
    (hv : toLp 2 v ∉ S) : 0 < ‖(residual S v).ofLp‖ := by
  apply norm_pos_iff.mpr
  intro he
  apply hv
  apply (residual_eq_zero_iff S v).mp
  ext i
  exact congrFun he i

private theorem real_dotProduct_cast (a z : Fin p → ℤ) :
    realCoordinates a ⬝ᵥ realCoordinates z = (a ⬝ᵥ z : ℤ) := by
  simp [dotProduct, realCoordinates]

private theorem real_dotProduct_error (a : Fin p → ℤ) (x y : Fin p → ℝ) (ε : ℝ)
    (h : ∀ i, |x i - y i| ≤ ε) :
    |realCoordinates a ⬝ᵥ x - realCoordinates a ⬝ᵥ y| ≤
      (∑ i, |(a i : ℝ)|) * ε := by
  calc
    _ = |∑ i, (a i : ℝ) * (x i - y i)| := by
      simp [dotProduct, realCoordinates, mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i, |(a i : ℝ) * (x i - y i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |(a i : ℝ)| * ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

private theorem small_error_sign {r c : ℝ} {k : ℤ} (hc : 0 < c) (hk : k ≠ 0)
    (he : |c * r - k| < 1) : sign k = sign r := by
  rcases hk.lt_or_gt with hneg | hpos
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    have h' := (abs_lt.mp he).2
    have hcr : c * r < 0 := by linarith
    have hr : r < 0 := by
      by_contra! hr
      linarith [mul_nonneg hc.le hr]
    rw [sign_neg hneg, sign_neg hr]
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have h' := (abs_lt.mp he).1
    have hcr : 0 < c * r := by linarith
    have hr : 0 < r := (mul_pos_iff_of_pos_left hc).mp hcr
    rw [sign_pos hpos, sign_pos hr]

/-- Integer scalar products agreeing with a positive rescaling up to an error below one
have the correct sign whenever they do not vanish. -/
theorem roundingDirection_sign (S : Submodule ℝ (EuclideanSpace ℝ (Fin p)))
    (v : Fin p → ℝ) (hv : toLp 2 v ∉ S) (q : ℕ) (hq : 0 < q) (z a : Fin p → ℤ)
    (ε : ℝ) (he : ∀ i, |(q : ℝ) * roundingDirection S v i - z i| ≤ ε)
    (hsmall : (∑ i, |(a i : ℝ)|) * ε < 1)
    (hvanish : ∀ x ∈ S, realCoordinates a ⬝ᵥ x.ofLp = 0) (hdot : a ⬝ᵥ z ≠ 0) :
    sign (a ⬝ᵥ z) = sign (realCoordinates a ⬝ᵥ v) := by
  have hnorm := infNorm_residual_pos S v hv
  have hres : realCoordinates a ⬝ᵥ (residual S v).ofLp = realCoordinates a ⬝ᵥ v := by
    change realCoordinates a ⬝ᵥ (v - (S.starProjection (toLp 2 v)).ofLp) = _
    rw [dotProduct_sub, hvanish _ (S.starProjection_apply_mem _), sub_zero]
  have hscale : realCoordinates a ⬝ᵥ (fun i => (q : ℝ) * roundingDirection S v i) =
      ((q : ℝ) / ‖(residual S v).ofLp‖) * (realCoordinates a ⬝ᵥ v) := by
    rw [← hres, dotProduct, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [roundingDirection]
    ring
  have h := (real_dotProduct_error a _ (realCoordinates z) ε he).trans_lt hsmall
  rw [hscale, real_dotProduct_cast] at h
  apply small_error_sign (div_pos (Nat.cast_pos.mpr hq) hnorm) hdot h


/-- Each coordinate of the normalized residual lies in the unit interval in absolute value. -/
theorem abs_roundingDirection_le_one (S : Submodule ℝ (EuclideanSpace ℝ (Fin p)))
    (v : Fin p → ℝ) (i : Fin p) : |roundingDirection S v i| ≤ 1 := by
  by_cases h : (residual S v).ofLp = 0
  · simp [roundingDirection, h]
  · rw [roundingDirection, abs_div, abs_of_nonneg (norm_nonneg _),
      div_le_one (norm_pos_iff.mpr h)]
    exact (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm (residual S v).ofLp i)

/-- The error estimate forces the new integer vector outside the earlier subspace. -/
theorem roundingDirection_not_mem (S : Submodule ℝ (EuclideanSpace ℝ (Fin p)))
    (v : Fin p → ℝ) (hv : toLp 2 v ∉ S) (q : ℕ) (hq : 0 < q) (z : Fin p → ℤ)
    (ε : ℝ) (he : ∀ i, |(q : ℝ) * roundingDirection S v i - z i| ≤ ε)
    (hsmall : (p : ℝ) * ε ^ 2 < 1) : toLp 2 (realCoordinates z) ∉ S := by
  let w := residual S v
  let c : ℝ := (q : ℝ) / ‖w.ofLp‖
  let x := c • w
  let y := toLp 2 (realCoordinates z)
  have hn : 0 < ‖w.ofLp‖ := infNorm_residual_pos S v hv
  have hc : 0 < c := div_pos (Nat.cast_pos.mpr hq) hn
  have hnorm : ‖w.ofLp‖ ≤ ‖w‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr (PiLp.norm_apply_le w)
  have hx : 1 ≤ ‖x‖ := calc
    (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    _ = c * ‖w.ofLp‖ := (div_mul_cancel₀ _ hn.ne').symm
    _ ≤ c * ‖w‖ := mul_le_mul_of_nonneg_left hnorm hc.le
    _ = ‖x‖ := by rw [show ‖x‖ = ‖c‖ * ‖w‖ from norm_smul c w, Real.norm_eq_abs, abs_of_pos hc]
  have herror (i : Fin p) : ‖(x - y) i‖ ≤ ε := by
    rw [Real.norm_eq_abs]
    convert he i using 2
    change c * w i - z i = (q : ℝ) * (w i / ‖w.ofLp‖) - z i
    dsimp [c]
    ring
  have hdist : ‖x - y‖ ^ 2 < 1 := calc
    _ = ∑ i, ‖(x - y) i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
    _ ≤ ∑ _i : Fin p, ε ^ 2 :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (herror i) 2
    _ = (p : ℝ) * ε ^ 2 := by simp
    _ < 1 := hsmall
  intro hy
  have hperp : inner ℝ w y = 0 := Submodule.starProjection_inner_eq_zero _ _ hy
  have hxy : inner ℝ x y = 0 := by simp [x, inner_smul_left, hperp]
  have hpyth := norm_sub_sq_eq_norm_sq_add_norm_sq_real hxy
  nlinarith [sq_nonneg ‖y‖, sq_nonneg (‖x‖ - 1)]

/-- One projection-and-rounding step adds an independent integer direction and
preserves every newly determined sign for the paper's precision `1/(4 p M)`. -/
theorem roundingProjectionStep (S : Submodule ℝ (EuclideanSpace ℝ (Fin p)))
    (v : Fin p → ℝ) (hv : toLp 2 v ∉ S) {M : ℕ} (hp : 0 < p) (hM : 0 < M)
    (q : ℕ) (hq : 0 < q) (z : Fin p → ℤ)
    (he : ∀ i, |(q : ℝ) * roundingDirection S v i - z i| ≤ 1 / (4 * (p : ℝ) * M)) :
    toLp 2 (realCoordinates z) ∉ S ∧
      ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
        (∀ x ∈ S, realCoordinates a ⬝ᵥ x.ofLp = 0) → a ⬝ᵥ z ≠ 0 →
        sign (a ⬝ᵥ z) = sign (realCoordinates a ⬝ᵥ v) := by
  let ε : ℝ := 1 / (4 * (p : ℝ) * M)
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεp : (p : ℝ) * ε ≤ 1 / 4 := by
    dsimp [ε]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
    nlinarith [mul_nonneg (show 0 ≤ (p : ℝ) by positivity) (sub_nonneg.mpr hM')]
  have hεM : (M : ℝ) * ε ≤ 1 / 4 := by
    dsimp [ε]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
    nlinarith [mul_nonneg (show 0 ≤ (M : ℝ) by positivity) (sub_nonneg.mpr hp')]
  have hεle : ε ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hp') hε.le]
  constructor
  · apply roundingDirection_not_mem S v hv q hq z ε he
    calc (p : ℝ) * ε ^ 2 = ((p : ℝ) * ε) * ε := by ring
      _ ≤ (1 / 4) * 1 := mul_le_mul hεp hεle hε.le (by norm_num)
      _ < 1 := by norm_num
  · intro a ha hvanish hdot
    apply roundingDirection_sign S v hv q hq z a ε he _ hvanish hdot
    have ha' : (∑ i, |(a i : ℝ)|) ≤ (M : ℝ) := by exact_mod_cast ha
    exact ((mul_le_mul_of_nonneg_right ha' hε.le).trans hεM).trans_lt (by norm_num)

end Lattice
end LinearProgramming
end Optimization
end OAI
