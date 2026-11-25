import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
# Area of a boundary strip in a hyperbolic polygon

The last motion of Lemma 6.1 rounds each endpoint to its tile site. The
geometric input is that an `r`-neighborhood of finitely many geodesic sides
has area `O(r)`. We bound an actual hyperbolic ball using Mathlib's invariant
area measure `dx dy / y²`, then cover each unit-speed side with balls.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Real Metric MeasureTheory Set
open scoped ENNReal NNReal

private theorem sinh_le_cosh_one_mul {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    sinh r ≤ cosh 1 * r := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := Real.sinh) (f' := Real.cosh) (a := 0) (b := 1) (C := cosh 1)
    (fun x _ => (hasDerivAt_sinh x).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs, abs_of_pos (cosh_pos _)]; exact
      cosh_le_cosh.mpr (by simpa [abs_of_nonneg hx.1] using hx.2.le)) r hr
  simpa [Real.norm_eq_abs, abs_of_nonneg (sinh_nonneg_iff.mpr hr.1)] using h

/-- A uniform quadratic upper bound on the area of an actual hyperbolic ball,
independent of its height in the upper half-plane. -/
theorem hyperbolic_ball_area_le (z : UpperHalfPlane) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    volume (closedBall z r) ≤ ENNReal.ofReal ((exp 1 * cosh 1)^2 * Real.pi * r^2) := by
  let region := ((↑) : UpperHalfPlane → ℂ) '' closedBall z r
  let A := exp 1 / z.im
  have hA : 0 ≤ A := (div_pos (exp_pos _) z.im_pos).le
  have hrad : 0 ≤ z.im * sinh r := mul_nonneg z.im_pos.le (sinh_nonneg_iff.mpr hr.1)
  have hf (x : ℂ) (hx : x ∈ region) :
      (↑((1 / ‖x.im‖₊)^2 : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal (A^2) := by
    obtain ⟨w, hw, rfl⟩ := hx
    have hlog := (UpperHalfPlane.dist_log_im_le w z).trans hw
    rw [Real.dist_eq, abs_le] at hlog
    have hratio : z.im ≤ exp 1 * w.im := by
      rw [← Real.exp_log z.im_pos, ← Real.exp_log w.im_pos, ← exp_add, Real.exp_le_exp]
      linarith [hlog.1, hr.2]
    have hrecip : 1 / w.im ≤ A := (div_le_div_iff₀ w.im_pos z.im_pos).mpr (by simpa using hratio)
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    change (↑((1 / ‖w.im‖₊)^2 : ℝ≥0) : ℝ) ≤ A^2
    push_cast
    rw [Real.norm_eq_abs, abs_of_pos w.im_pos]
    exact pow_le_pow_left₀ (one_div_nonneg.mpr w.im_pos.le) hrecip 2
  rw [UpperHalfPlane.volume_eq_lintegral]
  calc
    _ ≤ ∫⁻ _ : ℂ in region, ENNReal.ofReal (A^2) :=
      setLIntegral_mono measurable_const hf
    _ = ENNReal.ofReal (A^2) * ENNReal.ofReal (z.im * sinh r)^2 * NNReal.pi := by
      simp [region, UpperHalfPlane.image_coe_closedBall, mul_assoc]
    _ = ENNReal.ofReal ((exp 1 * sinh r)^2 * Real.pi) := by
      rw [← ENNReal.ofReal_pow hrad, ← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_coe_nnreal (p := NNReal.pi), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [A]
      rw [← mul_pow, ← mul_assoc, div_mul_cancel₀ _ z.im_ne_zero]
    _ ≤ ENNReal.ofReal ((exp 1 * cosh 1)^2 * Real.pi * r^2) := by
      apply ENNReal.ofReal_le_ofReal
      have h := pow_le_pow_left₀ (mul_nonneg (exp_pos 1).le (sinh_nonneg_iff.mpr hr.1))
        (mul_le_mul_of_nonneg_left (sinh_le_cosh_one_mul hr) (exp_pos 1).le) 2
      convert mul_le_mul_of_nonneg_right h Real.pi_pos.le using 1
      ring

/-- Points within distance `r` of some point on a parametrized side. -/
def sideStrip (γ : ℝ → UpperHalfPlane) (L r : ℝ) : Set UpperHalfPlane :=
  {z | ∃ t ∈ Icc (0 : ℝ) L, dist z (γ t) ≤ r}

/-- A side of length `L` needs at most `⌊L/r⌋ + 1` radius-`2r` balls to
cover its radius-`r` strip. The total area is linear in `r`. -/
theorem sideStrip_area_le (γ : ℝ → UpperHalfPlane) (hγ : LipschitzWith 1 γ)
    {L r : ℝ} (hL : 0 ≤ L) (hr : 0 < r) (hr1 : 2*r ≤ 1) :
    volume (sideStrip γ L r) ≤
      ENNReal.ofReal (4 * (exp 1 * cosh 1)^2 * Real.pi * (L+1) * r) := by
  let K := ⌊L / r⌋₊ + 1
  let ballAt (i : Fin K) := closedBall (γ ((i : ℕ) * r)) (2*r)
  have hc : sideStrip γ L r ⊆ ⋃ i : Fin K, ballAt i := by
    intro z hz
    obtain ⟨t, ht, hd⟩ := hz
    let k := ⌊t / r⌋₊
    have hk : k < K := Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hr.le))
    refine mem_iUnion.mpr ⟨⟨k,hk⟩, ?_⟩
    have hlo : (k : ℝ) * r ≤ t :=
      (le_div_iff₀ hr).mp (Nat.floor_le (div_nonneg ht.1 hr.le))
    have hup := (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (t / r))
    have hdγ := hγ.dist_le_mul t ((k : ℝ) * r)
    rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)] at hdγ
    change dist z (γ ((k : ℝ)*r)) ≤ 2*r
    linarith only [dist_triangle z (γ t) (γ ((k : ℝ)*r)), hd, hdγ, hup]
  let C := (exp 1 * cosh 1)^2 * Real.pi
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (i : Fin K) : volume (ballAt i) ≤ ENNReal.ofReal (C * (2*r)^2) :=
    hyperbolic_ball_area_le _ ⟨by positivity,hr1⟩
  have hK : (K : ℝ) * r ≤ L + r := by
    have h := (le_div_iff₀ hr).mp (Nat.floor_le (div_nonneg hL hr.le))
    dsimp [K]
    push_cast
    linarith
  calc
    _ ≤ volume (⋃ i : Fin K, ballAt i) := measure_mono hc
    _ ≤ ∑ i, volume (ballAt i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : Fin K, ENNReal.ofReal (C * (2*r)^2) := Finset.sum_le_sum fun i _ => hb i
    _ = ENNReal.ofReal ((K : ℝ) * (C * (2*r)^2)) := by
      simp [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hprod := mul_le_mul_of_nonneg_right (hK.trans (show L+r ≤ L+1 by linarith))
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC) hr.le)
      dsimp [C] at hprod ⊢
      linarith only [hprod]

/-- The full strip around finitely many geodesic sides of a polygon has
the same linear bound, with the sum of the side constants. -/
theorem polygonStrip_area_le {E : Type*} [Fintype E] (γ : E → ℝ → UpperHalfPlane)
    (L : E → ℝ) (hγ : ∀ e, LipschitzWith 1 (γ e)) (hL : ∀ e, 0 ≤ L e)
    {r : ℝ} (hr : 0 < r) (hr1 : 2*r ≤ 1) :
    volume (⋃ e, sideStrip (γ e) (L e) r) ≤
      ENNReal.ofReal ((∑ e, 4 * (exp 1 * cosh 1)^2 * Real.pi * (L e + 1)) * r) := by
  apply (measure_iUnion_fintype_le _ _).trans
  calc
    _ ≤ ∑ e, ENNReal.ofReal (4 * (exp 1 * cosh 1)^2 * Real.pi * (L e + 1) * r) :=
      Finset.sum_le_sum fun e _ => sideStrip_area_le _ (hγ e) (hL e) hr hr1
    _ = _ := by
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
      exact fun e _ => by have := hL e; positivity

end Epoch

end BorderVNP
end Computability
end OAI
