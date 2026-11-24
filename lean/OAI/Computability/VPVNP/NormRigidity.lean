import OAI.Computability.VPVNP.CrossingSpectralBound
import OAI.Computability.VPVNP.SpectralRealizable
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Tactic.Linarith

/-!
# Norm rigidity from the shifted crossing

The two flattening bounds in Theorem 3.1 give a geometric inequality on the
cost of placing the auxiliary wire endpoints. This file derives Lemma 3.2's
inner-product conclusion from that inequality. If the dual quadratic bound
fails at smooth points, both costs strictly decrease along suitable directions.
Dense differentiability of the norm supplies supporting functionals and extends
the estimate to arbitrary vectors.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace NormRigidity

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm's derivative at the opposite vector is the opposite functional. -/
theorem norm_deriv_neg {y : E} {g : E →L[ℝ] ℝ} (hg : HasFDerivAt (‖·‖) g y) :
    HasFDerivAt (‖·‖) (-g) (-y) := by
  simpa using hg.hasFDerivAt_norm_smul_neg (show (-1 : ℝ) < 0 by norm_num)

private theorem normAlongMotion {x z : E} {f : E →L[ℝ] ℝ}
    (hf : HasFDerivAt (‖·‖) f x) :
    HasDerivAt (fun ε : ℝ => ‖x - ε • z‖) (-f z) 0 := by
  have hl : HasDerivAt (fun ε : ℝ => x - ε • z) (-z) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const z).const_sub x
  simpa [Function.comp_def] using hf.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

/-- A negative derivative at zero forces a decrease for every sufficiently
small positive step, without any derivative assumptions away from zero. -/
theorem eventually_lt_of_deriv_neg {F : ℝ → ℝ} {d : ℝ}
    (hF : HasDerivAt F d 0) (hd : d < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε < F 0 := by
  filter_upwards [hF.tendsto_slope_zero_right.eventually (eventually_lt_nhds hd),
    self_mem_nhdsWithin] with ε hε hpos
  have hpos' : 0 < ε := hpos
  simp only [zero_add, smul_eq_mul] at hε
  by_contra! hle
  exact hε.not_ge (mul_nonneg (inv_nonneg.mpr hpos'.le) (sub_nonneg.mpr hle))

/-- A common movement of two endpoints decreases their weighted lengths even
after paying the linear cost for the new segment. -/
theorem weighted_norm_motion {x y : E} {f g : E →L[ℝ] ℝ}
    (hf : HasFDerivAt (‖·‖) f x) (hg : HasFDerivAt (‖·‖) g y)
    {t u b : ℝ} {z : E} (hlt : b * ‖z‖ < (t • f + u • g) z) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      t * ‖x - ε • z‖ + u * ‖y - ε • z‖ + ε * b * ‖z‖ < t * ‖x‖ + u * ‖y‖ := by
  have hF := (((normAlongMotion (z := z) hf).const_mul t).add
    ((normAlongMotion (z := z) hg).const_mul u)).add
    (((hasDerivAt_id' (0 : ℝ)).mul_const b).mul_const ‖z‖)
  have hd : t * (-f z) + u * (-g z) + 1 * b * ‖z‖ < 0 := by
    simp only [add_apply, smul_apply, smul_eq_mul] at hlt
    linarith
  simpa using eventually_lt_of_deriv_neg hF hd

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Norm derivatives approximate the norm from below in every direction. -/
theorem exists_norm_derivative_approx (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ (z : E) (f : E →L[ℝ] ℝ), HasFDerivAt (‖·‖) f z ∧
      f z = ‖z‖ ∧ ‖f‖ ≤ 1 ∧ ‖x‖ - ε ≤ f x := by
  obtain ⟨z, hz, hxz⟩ := (dense_differentiableAt_norm (E := E)).exists_dist_lt x (half_pos hε)
  change DifferentiableAt ℝ (‖·‖) z at hz
  let f := fderiv ℝ (fun v : E => ‖v‖) z
  have hf : ‖f‖ ≤ 1 := NNReal.coe_one ▸
    norm_fderiv_le_of_lipschitz ℝ (x₀ := z) lipschitzWith_one_norm
  refine ⟨z, f, hz.hasFDerivAt, hz.fderiv_norm_self, hf, ?_⟩
  have hfxz : f z - f x ≤ ‖z - x‖ := calc
    f z - f x = f (z - x) := (map_sub f z x).symm
    _ ≤ ‖f (z - x)‖ := _root_.le_abs_self _
    _ ≤ ‖f‖ * ‖z - x‖ := f.le_opNorm _
    _ ≤ 1 * ‖z - x‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg _)
    _ = _ := one_mul _
  have hnxz : ‖x‖ - ‖z‖ ≤ ‖x - z‖ := norm_sub_norm_le x z
  rw [norm_sub_rev] at hfxz
  have hfz : f z = ‖z‖ := hz.fderiv_norm_self
  rw [dist_eq_norm] at hxz
  linarith

end

/-- The two crossing cuts use opposite partners at the terminal marked by `y`.
The central-wire costs are the two square roots in Theorem 3.1. -/
def CrossingPlacement (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∀ (x y zp zm : E) (t u δ : ℝ), 0 < t → 0 < u →
    -(t^2 + u^2) < δ → δ < t^2 + u^2 →
    t * ‖x‖ + u * ‖y‖ ≤ max
      (t * ‖x - zp‖ + u * ‖y - zp‖ + Real.sqrt (t^2 + u^2 + δ) * ‖zp‖)
      (t * ‖x - zm‖ + u * ‖-y - zm‖ + Real.sqrt (t^2 + u^2 - δ) * ‖zm‖)

private theorem witness_of_lt_norm (F : E →L[ℝ] ℝ) (c : ℝ) (hc : 0 ≤ c) (hF : c < ‖F‖) :
    ∃ z : E, c * ‖z‖ < F z := by
  by_contra! hall
  apply (not_lt_of_ge (F.opNorm_le_bound hc ?_)) hF
  intro z
  rw [Real.norm_eq_abs, abs_le]
  have hn := hall (-z)
  rw [map_neg, norm_neg] at hn
  exact ⟨by linarith, hall z⟩

private theorem choose_displacement {S A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hA₂ : A^2 ≤ 2*S) (hB₂ : B^2 ≤ 2*S)
    (hbad : 2*S < A^2 + B^2) :
    ∃ δ : ℝ, -S < δ ∧ δ < S ∧ Real.sqrt (S+δ) < A ∧ Real.sqrt (S-δ) < B := by
  let δ := (A^2 - B^2) / 2
  have h₁ : -S < δ := by dsimp [δ]; linarith
  have h₂ : δ < S := by dsimp [δ]; linarith
  refine ⟨δ, h₁, h₂, ?_, ?_⟩
  · apply (Real.sqrt_lt' (by nlinarith : 0 < A)).mpr
    dsimp [δ]
    linarith
  · apply (Real.sqrt_lt' (by nlinarith : 0 < B)).mpr
    dsimp [δ]
    linarith

private theorem norm_smul_le_scalar (f : E →L[ℝ] ℝ) {t : ℝ} (ht : 0 ≤ t) (hf : ‖f‖ ≤ 1) :
    ‖t • f‖ ≤ t := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  simpa using (mul_le_mul_of_nonneg_left hf ht)

/-- A strict failure of the dual norm inequality yields simultaneous strict descent
directions for the two crossing costs. -/
theorem crossing_descent_directions (f g : E →L[ℝ] ℝ) {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1)
    (hbad : 2 * (t^2 + u^2) < ‖t • f + u • g‖^2 + ‖t • f - u • g‖^2) :
    ∃ (δ : ℝ) (zp zm : E), -(t^2+u^2) < δ ∧ δ < t^2+u^2 ∧
      Real.sqrt (t^2+u^2+δ)*‖zp‖ < (t • f + u • g) zp ∧
      Real.sqrt (t^2+u^2-δ)*‖zm‖ < (t • f - u • g) zm := by
  have hn := add_le_add (norm_smul_le_scalar f ht.le hf) (norm_smul_le_scalar g hu.le hg)
  have hquad : (t+u)^2 ≤ 2*(t^2+u^2) := by nlinarith only [sq_nonneg (t-u)]
  have hplus : ‖t • f + u • g‖ ≤ t+u := (norm_add_le _ _).trans hn
  have hminus : ‖t • f - u • g‖ ≤ t+u := (norm_sub_le _ _).trans hn
  obtain ⟨δ, hδl, hδr, hp, hm⟩ := choose_displacement (norm_nonneg _) (norm_nonneg _)
    ((pow_le_pow_left₀ (norm_nonneg _) hplus 2).trans hquad)
    ((pow_le_pow_left₀ (norm_nonneg _) hminus 2).trans hquad) hbad
  obtain ⟨zp, hzp⟩ := witness_of_lt_norm _ _ (Real.sqrt_nonneg _) hp
  obtain ⟨zm, hzm⟩ := witness_of_lt_norm _ _ (Real.sqrt_nonneg _) hm
  exact ⟨δ, zp, zm, hδl, hδr, hzp, hzm⟩

/-- A placement satisfying the crossing inequality forces the dual quadratic
estimate on any two derivatives of the norm, as in equation (3.1). -/
theorem dual_bound_of_placement (hp : CrossingPlacement E) (x y : E)
    (f g : E →L[ℝ] ℝ) (hf : HasFDerivAt (‖·‖) f x) (hg : HasFDerivAt (‖·‖) g y)
    (hf' : ‖f‖ ≤ 1) (hg' : ‖g‖ ≤ 1) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    ‖t • f + u • g‖^2 + ‖t • f - u • g‖^2 ≤ 2 * (t^2 + u^2) := by
  rcases ht.eq_or_lt with h | ht
  · subst t
    have hle := pow_le_pow_left₀ (norm_nonneg _) (norm_smul_le_scalar g hu hg') 2
    simpa only [zero_smul, zero_add, zero_sub, norm_neg, zero_pow (by decide : 2 ≠ 0), two_mul]
      using add_le_add hle hle
  rcases hu.eq_or_lt with h | hu
  · subst u
    have hle := pow_le_pow_left₀ (norm_nonneg _) (norm_smul_le_scalar f ht.le hf') 2
    simpa only [zero_smul, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), two_mul]
      using add_le_add hle hle
  by_contra! hbad
  obtain ⟨δ, zp, zm, hδl, hδr, hz, hw⟩ := crossing_descent_directions f g ht hu hf' hg' hbad
  have hw' : √(t^2 + u^2 - δ) * ‖zm‖ < (t • f + u • (-g)) zm := by
    simpa [sub_eq_add_neg] using hw
  have hnear : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hplus, hminus⟩ :=
    (hnear.and ((weighted_norm_motion hf hg hz).and
      (weighted_norm_motion hf (norm_deriv_neg hg) hw'))).exists
  have hpos : 0 < ε := hε
  have hplacement := hp x y (ε • zp) (ε • zm) t u δ ht hu hδl hδr
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hpos] at hplacement
  rw [norm_neg] at hminus
  rw [le_max_iff] at hplacement
  rcases hplacement with h | h <;> linarith

section

private theorem eval_le_squares (f : E →L[ℝ] ℝ) (x : E) :
    f x ≤ ‖f‖ ^ 2 / 4 + ‖x‖ ^ 2 := by
  have h := (le_abs_self (f x)).trans (f.le_opNorm x)
  nlinarith only [h, sq_nonneg (‖f‖ - 2 * ‖x‖)]

variable (D : Set (E →L[ℝ] ℝ))
    (hD : ∀ x : E, ∀ ε : ℝ, 0 < ε → ∃ f ∈ D, ‖f‖ ≤ 1 ∧ ‖x‖ - ε ≤ f x)
    (hdual : ∀ f ∈ D, ∀ g ∈ D, ∀ t u : ℝ, 0 ≤ t → 0 ≤ u →
      ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ 2 * (t ^ 2 + u ^ 2))

include hD hdual in
/-- The two dual combinations bound the weighted evaluations at `a + b` and `a - b`.
Approximate support functionals then give the upper half of the parallelogram law. -/
theorem parallelogram_le_of_dual_bound (a b : E) :
    ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  let t := ‖a + b‖
  let u := ‖a - b‖
  have ht : 0 ≤ t := norm_nonneg _
  have hu : 0 ≤ u := norm_nonneg _
  change t ^ 2 + u ^ 2 ≤ _
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  let δ := ε / (2 * (t + u) + 1)
  have hpos : 0 < 2 * (t + u) + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hpos
  have hscale : δ * (2 * (t + u) + 1) = ε := div_mul_cancel₀ ε hpos.ne'
  obtain ⟨f, hf, _, hfx⟩ := hD (a + b) δ hδ
  obtain ⟨g, hg, _, hgy⟩ := hD (a - b) δ hδ
  change t - δ ≤ f (a + b) at hfx
  change u - δ ≤ g (a - b) at hgy
  have happrox := add_le_add (mul_le_mul_of_nonneg_left hfx ht)
    (mul_le_mul_of_nonneg_left hgy hu)
  have heval := add_le_add (eval_le_squares (t • f + u • g) a)
    (eval_le_squares (t • f - u • g) b)
  simp only [map_add, map_sub] at happrox
  simp only [add_apply, sub_apply,
    smul_apply, smul_eq_mul] at heval
  linarith only [happrox, heval, hdual f hf g hg t u ht hu, hscale, hδ]

include hD hdual in
/-- Applying the upper parallelogram estimate to the sum and difference gives equality. -/
theorem parallelogram_of_dual_bound (a b : E) :
    ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  apply le_antisymm (parallelogram_le_of_dual_bound D hD hdual a b)
  have h := parallelogram_le_of_dual_bound D hD hdual (a + b) (a - b)
  have ha : a + b + (a - b) = (2 : ℝ) • a := by rw [two_smul]; abel
  have hb : a + b - (a - b) = (2 : ℝ) • b := by rw [two_smul]; abel
  rw [ha, hb, norm_smul, norm_smul] at h
  norm_num at h
  linarith only [h]

include hD hdual in
/-- The real norm comes from an inner product whenever its approximate support
functionals satisfy the dual estimate (3.1). -/
theorem innerProduct_of_dual_bound : Nonempty (InnerProductSpace ℝ E) := by
  exact ⟨InnerProductSpace.ofNorm ℝ fun a b ↦ by
    simpa only [sq] using parallelogram_of_dual_bound D hD hdual a b⟩

end

/-- The geometric implication of Lemma 3.2. In a finite-dimensional real
space the two crossing placement costs force the given norm to be Euclidean. -/
theorem innerProduct_of_placement [FiniteDimensional ℝ E] (hp : CrossingPlacement E) :
    Nonempty (InnerProductSpace ℝ E) := by
  let D : Set (E →L[ℝ] ℝ) := {f | ‖f‖ ≤ 1 ∧ ∃ x, HasFDerivAt (‖·‖) f x}
  apply innerProduct_of_dual_bound D
  · intro v ε hε
    obtain ⟨z, f, hz, _, hf, hv⟩ := exists_norm_derivative_approx v hε
    exact ⟨f, ⟨hf, z, hz⟩, hf, hv⟩
  · rintro f ⟨hf, x, hx⟩ g ⟨hg, y, hy⟩ t u ht hu
    exact dual_bound_of_placement hp x y f g hx hy hf hg ht hu

/-- The cost of adding two tensor summands contributes at most one bit beyond
the larger base-two exponent. -/
theorem exponent_le_max_add_one {A P Q : ℝ}
    (h : (2 : ℝ)^A ≤ (2 : ℝ)^P + (2 : ℝ)^Q) : A ≤ max P Q + 1 := by
  apply (Real.rpow_le_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)).mp
  calc
    (2 : ℝ)^A ≤ (2 : ℝ)^P + (2 : ℝ)^Q := h
    _ ≤ (2 : ℝ)^(max P Q) + (2 : ℝ)^(max P Q) := add_le_add
      ((Real.rpow_le_rpow_left_iff (by norm_num)).mpr (le_max_left P Q))
      ((Real.rpow_le_rpow_left_iff (by norm_num)).mpr (le_max_right P Q))
    _ = (2 : ℝ)^(max P Q + 1) := by rw [Real.rpow_add_one (by norm_num)]; ring

/-- For two exponentially scaled wire costs, subadditivity implies that the
target rate is bounded by the larger limiting cost. -/
theorem limit_le_max_of_two_powers {A P Q : ℕ → ℝ} {a p q : ℝ}
    (hA : Tendsto A atTop (𝓝 a)) (hP : Tendsto P atTop (𝓝 p)) (hQ : Tendsto Q atTop (𝓝 q))
    (h : ∀ᶠ n : ℕ in atTop, (2 : ℝ)^((n : ℝ) * A n) ≤
      (2 : ℝ)^((n : ℝ) * P n) + (2 : ℝ)^((n : ℝ) * Q n)) : a ≤ max p q := by
  have hlim : Tendsto (fun n : ℕ => max (P n) (Q n) + 1 / n) atTop (𝓝 (max p q)) := by
    simpa using (hP.max hQ).add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  apply le_of_tendsto_of_tendsto hA hlim
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hbound := exponent_le_max_add_one hn
  rw [← mul_max_of_nonneg _ _ hn'.le] at hbound
  apply (mul_le_mul_iff_right₀ hn').mp
  rwa [mul_add, mul_one_div_cancel hn'.ne']

private theorem pow_scaled_log_rate {n : ℕ} {d : ℝ} (hn : 0 < n) (hd : 0 < d) (c : ℝ) :
    (2 : ℝ)^((n : ℝ) * (c * (Real.logb 2 d / n))) = d^c := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show (n : ℝ) * (c * (Real.logb 2 d / n)) = Real.logb 2 d * c by field_simp]
  rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hd]

/-- The four-terminal wire inequality at a common realization scale. The
two original wires have terminal-to-terminal lengths `2*x0` and `2*y0`. In each placement
the terminal links have lengths `xp,yp` or `xm,ym` and the two centers have
distances `2*ep` and `2*em`. The two crossing ranks may have different exponential rates. -/
theorem crossingPlacement_cost_limit {X Y Rplus Rminus : ℕ → ℕ}
    {t u rp rm σ x0 y0 ep em xp yp xm ym : ℝ} (hσ : 0 < σ)
    (hX : Tendsto (fun n : ℕ => Real.logb 2 (X n) / n) atTop (𝓝 t))
    (hY : Tendsto (fun n : ℕ => Real.logb 2 (Y n) / n) atTop (𝓝 u))
    (hp : Tendsto (fun n : ℕ => Real.logb 2 (Rplus n) / n) atTop (𝓝 rp))
    (hm : Tendsto (fun n : ℕ => Real.logb 2 (Rminus n) / n) atTop (𝓝 rm))
    (hpos : ∀ᶠ n in atTop, 0 < X n ∧ 0 < Y n ∧ 0 < Rplus n ∧ 0 < Rminus n)
    (hcost : ∀ᶠ n in atTop,
      (X n : ℝ)^(2*σ*x0) * (Y n : ℝ)^(2*σ*y0) ≤
      (X n : ℝ)^(2*σ*xp) * (Y n : ℝ)^(2*σ*yp) * (Rplus n : ℝ)^(2*σ*ep) +
      (X n : ℝ)^(2*σ*xm) * (Y n : ℝ)^(2*σ*ym) * (Rminus n : ℝ)^(2*σ*em)) :
    t * x0 + u * y0 ≤ max (t * xp + u * yp + ep * rp) (t * xm + u * ym + em * rm) := by
  have bound := limit_le_max_of_two_powers
    ((hX.const_mul (2*σ*x0)).add (hY.const_mul (2*σ*y0)))
    (((hX.const_mul (2*σ*xp)).add (hY.const_mul (2*σ*yp))).add (hp.const_mul (2*σ*ep)))
    (((hX.const_mul (2*σ*xm)).add (hY.const_mul (2*σ*ym))).add (hm.const_mul (2*σ*em))) (by
      filter_upwards [hpos, hcost, eventually_gt_atTop (0 : ℕ)] with n hn hc hnpos
      obtain ⟨hx, hy, hplus, hminus⟩ := hn
      have hx' : 0 < (X n : ℝ) := by exact_mod_cast hx
      have hy' : 0 < (Y n : ℝ) := by exact_mod_cast hy
      have hp' : 0 < (Rplus n : ℝ) := by exact_mod_cast hplus
      have hm' : 0 < (Rminus n : ℝ) := by exact_mod_cast hminus
      simpa only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, mul_add,
        Real.rpow_add (show (0 : ℝ) < 2 by norm_num), pow_scaled_log_rate hnpos hx',
        pow_scaled_log_rate hnpos hy', pow_scaled_log_rate hnpos hp', pow_scaled_log_rate hnpos hm']
        using hc)
  apply (mul_le_mul_iff_right₀ (show 0 < 2*σ by positivity)).mp
  rw [mul_max_of_nonneg _ _ (show 0 ≤ 2*σ by positivity)]
  ring_nf at bound ⊢
  exact bound

/-- The spectral inequality for the two placements of a finite, integer crossing.
The shared scale belongs to the realization of the eight points. -/
def FiniteCrossingCost (x y zp zm : E) (σ : ℝ) : Prop :=
  ∀ {X Y P M : ℕ}, 0 < X → 0 < Y → 0 < P → 0 < M →
    Crossing.IntegralCrossing X Y P M →
    (X : ℝ)^(2*σ*‖x‖) * (Y : ℝ)^(2*σ*‖y‖) ≤
      (X : ℝ)^(2*σ*‖x-zp‖) * (Y : ℝ)^(2*σ*‖y-zp‖) * (P : ℝ)^(2*σ*‖zp‖) +
      (X : ℝ)^(2*σ*‖x-zm‖) * (Y : ℝ)^(2*σ*‖-y-zm‖) * (M : ℝ)^(2*σ*‖zm‖)

private theorem eventually_pos_of_log_rate {D : ℕ → ℕ} {d : ℝ} (hd : 0 < d)
    (hD : Tendsto (fun n : ℕ => Real.logb 2 (D n) / n) atTop (𝓝 d)) :
    ∀ᶠ n in atTop, 0 < D n := by
  filter_upwards [hD.eventually_const_lt hd] with n hn
  by_contra! h
  rw [Nat.le_zero.mp h] at hn
  simp at hn

omit [NormedSpace ℝ E] in
/-- Theorem 3.1 turns the finite wire-cost inequality at one common realization
scale into the two geometric placement costs of Lemma 3.2. -/
theorem crossingPlacement_of_finiteCosts
    (hcost : ∀ x y zp zm : E, ∃ σ : ℝ, 0 < σ ∧ FiniteCrossingCost x y zp zm σ) :
    CrossingPlacement E := by
  intro x y zp zm t u δ ht hu hδl hδr
  obtain ⟨σ, hσ, hwire⟩ := hcost x y zp zm
  obtain ⟨X, Y, P, M, hX, hY, hP, hM, hfactors⟩ := Crossing.shiftedCrossing t u δ ht hu hδl hδr
  have hpos := (eventually_pos_of_log_rate ht hX).and ((eventually_pos_of_log_rate hu hY).and
    ((eventually_pos_of_log_rate (Real.sqrt_pos.mpr (by linarith)) hP).and
     (eventually_pos_of_log_rate (Real.sqrt_pos.mpr (by linarith)) hM)))
  have h := crossingPlacement_cost_limit (x0 := ‖x‖) (y0 := ‖y‖) (ep := ‖zp‖) (em := ‖zm‖)
    (xp := ‖x-zp‖) (yp := ‖y-zp‖) (xm := ‖x-zm‖) (ym := ‖-y-zm‖) hσ hX hY hP hM hpos (by
      filter_upwards [hpos] with n ⟨hx, hy, hp, hm⟩
      exact hwire hx hy hp hm (hfactors n).some)
  simpa only [mul_comm ‖zp‖, mul_comm ‖zm‖] using h

/-- A translate of one positive rescaling of a finite configuration lies
entirely in any prescribed nonempty open set. -/
theorem exists_homothety_mem {ι : Type*} [Finite ι] (p : ι → E) {U : Set E}
    (hU : IsOpen U) (hU' : U.Nonempty) :
    ∃ c : E, ∃ r : ℝ, 0 < r ∧ ∀ i, c + r • p i ∈ U := by
  obtain ⟨c, hc⟩ := hU'
  have hi (i : ι) : ∀ᶠ r in 𝓝[>] (0 : ℝ), c + r • p i ∈ U := by
    have hcont : Continuous (fun r : ℝ => c + r • p i) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hlim : Tendsto (fun r : ℝ => c + r • p i) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
      simpa [ContinuousWithinAt] using hcont.continuousWithinAt (s := Set.Ioi (0 : ℝ)) (x := 0)
    exact hlim.eventually (hU.mem_nhds hc)
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hp⟩ := (hpos.and (eventually_all.mpr hi)).exists
  exact ⟨c, r, hr, hp⟩

/-- A translated positive rescaling multiplies every pair distance by its scale. -/
theorem dist_homothety (c x y : E) {r : ℝ} (hr : 0 ≤ r) :
    dist (c + r • x) (c + r • y) = r * dist x y := by
  simp [dist_smul₀, Real.norm_of_nonneg hr]

/-- The two possible placements use eight roles. Roles 0 and 1 are the endpoints
of the first wire, 2 and 3 those of the second wire, and the last four are the
two pairs of auxiliary centers. The distances may vanish between distinct roles. -/
def EightPointCrossingCost (d : Fin 8 → Fin 8 → ℝ) : Prop :=
  ∀ {X Y P M : ℕ}, 0 < X → 0 < Y → 0 < P → 0 < M → Crossing.IntegralCrossing X Y P M →
    (X : ℝ)^(d 0 1) * (Y : ℝ)^(d 2 3) ≤
      (X : ℝ)^(d 0 4 + d 1 5) * (Y : ℝ)^(d 2 4 + d 3 5) * (P : ℝ)^(d 4 5) +
      (X : ℝ)^(d 0 6 + d 1 7) * (Y : ℝ)^(d 3 6 + d 2 7) * (M : ℝ)^(d 6 7)

private theorem dist_to_neg (x : E) : dist x (-x) = 2 * ‖x‖ := by
  rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ x, norm_smul]
  norm_num

/-- From scaled spectral costs on every finite configuration in an open set,
obtain the two placement inequalities on the whole normed space. -/
theorem placement_of_local_costs {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    (hcost : ∀ p : Fin 8 → E, (∀ i, p i ∈ U) →
      ∃ σ : ℝ, 0 < σ ∧ EightPointCrossingCost (fun i j => σ * dist (p i) (p j))) :
    CrossingPlacement E := by
  apply crossingPlacement_of_finiteCosts
  intro x y zp zm
  let p : Fin 8 → E := ![x, -x, y, -y, zp, -zp, zm, -zm]
  obtain ⟨c, r, hr, hc⟩ := exists_homothety_mem p hU hne
  obtain ⟨σ, hσ, hp⟩ := hcost (fun i => c + r • p i) hc
  refine ⟨σ*r, mul_pos hσ hr, ?_⟩
  intro X Y P M hx hy hP hM factor
  have hh := hp hx hy hP hM factor
  simp only [dist_homothety c _ _ hr.le] at hh
  change (X : ℝ)^(σ*(r*dist x (-x))) * (Y : ℝ)^(σ*(r*dist y (-y))) ≤
    (X : ℝ)^(σ*(r*dist x zp)+σ*(r*dist (-x) (-zp))) *
      (Y : ℝ)^(σ*(r*dist y zp)+σ*(r*dist (-y) (-zp))) * (P : ℝ)^(σ*(r*dist zp (-zp))) +
    (X : ℝ)^(σ*(r*dist x zm)+σ*(r*dist (-x) (-zm))) *
      (Y : ℝ)^(σ*(r*dist (-y) zm)+σ*(r*dist y (-zm))) * (M : ℝ)^(σ*(r*dist zm (-zm))) at hh
  have hflip : dist y (-zm) = dist (-y) zm := by simpa using (dist_neg_neg y (-zm)).symm
  simp only [dist_to_neg, dist_neg_neg, hflip] at hh
  simp only [dist_eq_norm] at hh
  convert hh using 1 <;> ring_nf

/-- A finite-dimensional norm is Euclidean if some nonempty open set satisfies
the two finite crossing costs at a common scale for every eight-point configuration. -/
theorem innerProduct_of_local_costs [FiniteDimensional ℝ E] {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty)
    (hcost : ∀ p : Fin 8 → E, (∀ i, p i ∈ U) →
      ∃ σ : ℝ, 0 < σ ∧ EightPointCrossingCost (fun i j => σ * dist (p i) (p j))) :
    Nonempty (InnerProductSpace ℝ E) :=
  innerProduct_of_placement (placement_of_local_costs hU hne hcost)

/-- A spectral point bounds the finite cost at any eight labelled tensor parties. -/
theorem eightPointCost_of_spectrum {k J : Type*} [Field k] [Fintype J]
    (F : WireTensor.SpectralPoint k J) (label : Fin 8 → J) :
    EightPointCrossingCost (fun i j => F.wireDistance (label i) (label j)) := by
  intro X Y P M hx hy hp hm f
  let term : Crossing.Terminal → J :=
    Sum.elim (fun b => if b then label 1 else label 0) (fun b => if b then label 3 else label 2)
  let cp := fun b : Bool => if b then label 5 else label 4
  let cm := fun b : Bool => if b then label 7 else label 6
  exact Crossing.crossing_spectral_inequality F term cp cm hx hy hp hm f

/-- Lemma 3.2. If each finite subset of a nonempty open set in a real normed
space is realized up to scale by spectral wires over the fixed field, the
space's norm comes from an inner product. The proof works in every finite
dimension, including the real normed planes of the lemma. -/
theorem norm_rigidity (k : Type*) [Field k] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hUn : U.Nonempty)
    (h : ∀ S : Finset E, (↑S : Set E) ⊆ U →
      WireTensor.RealizableUpToScale k (fun i j : S => dist i.val j.val)) :
    Nonempty (InnerProductSpace ℝ E) := by
  classical
  apply innerProduct_of_local_costs hU hUn
  intro p hp
  let S : Finset E := Finset.univ.image p
  have hSU : (↑S : Set E) ⊆ U := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hp i
  let l : Fin 8 → S := fun i => ⟨p i, Finset.mem_image_of_mem p (Finset.mem_univ _)⟩
  obtain ⟨w⟩ := (h S hSU).relabel l
  refine ⟨w.scale⁻¹, inv_pos.mpr w.scale_pos, ?_⟩
  have hd (i j : Fin 8) : w.scale⁻¹ * dist (p i) (p j) = w.spectrum.wireDistance (w.label i) (w.label j) := by
    have hd' : dist (p i) (p j) = w.scale * w.spectrum.wireDistance (w.label i) (w.label j) :=
      w.distances i j
    rw [hd', inv_mul_cancel_left₀ w.scale_pos.ne']
  simp only [hd]
  intro X Y P M hx hy hp hm f
  exact eightPointCost_of_spectrum w.spectrum w.label hx hy hp hm f

end NormRigidity

end VPVNP
end Computability
end OAI
