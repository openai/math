import OAI.LinearAlgebra.MatrixExponent.Rectangle.Threshold.Model
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

section
/-! # Optimizing the amount trimmed from the logarithmic output lengths -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Threshold
open Real

variable {b C u : ℝ}

private theorem upper {v : ℝ} (hp : 0 ≤ b + C * v) (hf : b + C * u ≤ (b + C * v) * (1 + (u - v) / 2)) :
    gain b C u ≤ gain b C v := by
  have h : max (b + C * u) 0 ≤ (b + C * v) * exp ((u - v) / 2) :=
    max_le (hf.trans (mul_le_mul_of_nonneg_left (by linarith [add_one_le_exp ((u - v) / 2)]) hp))
      (by positivity)
  unfold gain
  rw [max_eq_left hp]
  calc
    _ ≤ exp (-u) * ((b + C * v) * exp ((u - v) / 2)) ^ 2 / 4 := by gcongr
    _ = _ := by
      rw [mul_pow, ← exp_nat_mul, show (2 : ℕ) * ((u - v) / 2) = u - v by ring,
        mul_left_comm, ← exp_add, show -u + (u - v) = -v by ring]
      ring

/-- The maximum includes the boundary case of no trimming. -/
theorem maximum (b : ℝ) (hC : 0 < C) :
    let v := max 0 (2 - b / C)
    gain b C v = optimum b C ∧ IsGreatest {s | ∃ u : ℝ, 0 ≤ u ∧ gain b C u = s} (optimum b C) := by
  let v := max 0 (2 - b / C)
  have he : gain b C v = optimum b C ∧ ∀ u : ℝ, 0 ≤ u → gain b C u ≤ gain b C v := by
    by_cases h : b ≤ 2 * C
    · have hv : v = 2 - b / C := max_eq_right (sub_nonneg.mpr ((div_le_iff₀ hC).mpr h))
      have hp : b + C * v = 2 * C := by rw [hv]; field_simp; ring
      refine ⟨?_, fun u _ => upper (by linarith) ?_⟩
      · rw [optimum, ite_eq_left h, gain, hp, max_eq_left (by positivity), hv, neg_sub]
        ring
      · rw [hp]
        linarith
    · have hv : v = 0 := max_eq_left (sub_nonpos.mpr ((le_div_iff₀ hC).mpr (le_of_not_ge h)))
      rw [hv]
      refine ⟨by simp [optimum, h, gain, show 0 ≤ b by linarith], fun u hu => upper (by linarith) ?_⟩
      linarith [mul_le_mul_of_nonneg_right (le_of_not_ge h) hu]
  exact ⟨he.1, ⟨v, le_max_left _ _, he.1⟩, fun _ ⟨u, hu, heq⟩ => heq ▸ (he.2 u hu).trans_eq he.1⟩

theorem square_optimum {a : ℝ} (ha : 0 < a) (he : a ≤ Real.sqrt (exp 1)) :
    optimum (4 * log a) 1 = exp (-2) * a ^ 4 := by
  have h := log_le_log ha he
  rw [log_sqrt (by positivity), log_exp] at h
  rw [optimum, ite_eq_left (by linarith), one_pow, one_mul, div_one]
  rw [show 4 * log a - 2 = -2 + (4 : ℕ) * log a by ring, exp_add, exp_nat_mul, exp_log ha]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Threshold
end

section
/-!
# The harmonic threshold

The logarithms of the outer lengths are trimmed by fixed amounts.
All three logarithms may have errors tending to zero, as happens
when rounding the lengths to integers.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter
open scoped Topology

variable {x y s t b : ℝ} {k X Y Z : ℕ → ℝ}

private theorem side_ratio (hk : Tendsto k atTop atTop)
    (hX : Tendsto (fun n => X n - x * k n) atTop (𝓝 s)) :
    Tendsto (fun n => X n / k n) atTop (𝓝 x) := by
  have h := (hX.div_atTop hk).add_const x
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [hk.eventually_gt_atTop 0] with n hn
  field_simp
  ring

/-- At inner exponent `xy`, the excess over output area is of order
`1/k` or smaller. The limit includes the untrimmed case. -/
theorem shifted_threshold_limit (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (hk : Tendsto k atTop atTop)
    (hX : Tendsto (fun n => X n - x * k n) atTop (𝓝 (-s)))
    (hY : Tendsto (fun n => Y n - y * k n) atTop (𝓝 (-t)))
    (hZ : Tendsto (fun n => Z n - x * y * k n) atTop (𝓝 (b * (x * y)))) :
    Tendsto (fun n => k n * (U (X n) (Y n) (Z n) - X n - Y n)) atTop
      (𝓝 ((max (b + (y / x) * s + (x / y) * t) 0) ^ 2 / 4)) := by
  have h₁ := side_ratio hk hX
  have h₂ := side_ratio hk hY
  have h₃ := side_ratio hk hZ
  have hy' : y = 1 - x := by linarith
  let p n := (X n + Y n) * Z n - X n * Y n
  have hp : Tendsto (fun n => p n / k n) atTop (𝓝 ((x * y) * (b + (y / x) * s + (x / y) * t))) := by
    have h := (((h₁.add h₂).mul hZ).add ((h₂.const_sub (x * y)).mul hX)).add
      (hY.const_mul (x * y - x))
    rw [show (x + y) * (b * (x * y)) + (x * y - y) * (-s) + (x * y - x) * (-t) = (x * y) * (b + (y / x) * s + (x / y) * t) by
      field_simp; rw [hy']; ring] at h
    apply h.congr'
    filter_upwards [hk.eventually_gt_atTop 0] with n hn
    unfold p
    rw [hy']
    field_simp
    ring
  have h := ((hp.max (tendsto_const_nhds (x := (0 : ℝ)))).pow 2).div
    (((h₁.const_mul 4).mul h₂).mul h₃) (by positivity)
  let u := b + (y / x) * s + (x / y) * t
  have he : max ((x * y) * u) 0 = (x * y) * max u 0 := by
    rw [mul_max_of_nonneg _ _ (mul_pos hx hy).le, mul_zero]
  rw [he, show ((x * y) * max u 0) ^ 2 / (4 * x * y * (x * y)) = (max u 0) ^ 2 / 4 by field_simp] at h
  apply h.congr'
  have hzx : x * y < x := mul_lt_of_lt_one_right hx (by linarith)
  have hzy : x * y < y := mul_lt_of_lt_one_left hy (by linarith)
  filter_upwards [hk.eventually_gt_atTop 0, h₃.eventually_const_lt (mul_pos hx hy),
    h₃.eventually_lt h₁ hzx, h₃.eventually_lt h₂ hzy] with n hn hz hx' hy''
  have hZ₀ : 0 < Z n := (div_pos_iff_of_pos_right hn).mp hz
  have hZX := (div_lt_div_iff_of_pos_right hn).mp hx'
  have hZY := (div_lt_div_iff_of_pos_right hn).mp hy''
  have hX₀ := hZ₀.trans hZX
  have hY₀ := hZ₀.trans hZY
  have hmax : max (p n / k n) 0 = max (p n) 0 / k n := by
    simpa only [zero_div] using max_div_div_right hn.le (p n) 0
  dsimp only [Pi.div_apply]
  rw [hmax, U, ite_eq_left (le_min hZX.le hZY.le), benchmark]
  change _ = k n * (X n + Y n + (max (p n) 0) ^ 2 / (4 * X n * Y n * Z n) - X n - Y n)
  field_simp
  ring

/-- The derivative of the exponential gives the same scaled limit even
when the excess vanishes infinitely often. -/
theorem exp_shifted_threshold_limit (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (hk : Tendsto k atTop atTop)
    (hX : Tendsto (fun n => X n - x * k n) atTop (𝓝 (-s)))
    (hY : Tendsto (fun n => Y n - y * k n) atTop (𝓝 (-t)))
    (hZ : Tendsto (fun n => Z n - x * y * k n) atTop (𝓝 (b * (x * y)))) :
    Tendsto (fun n => k n * (Real.exp (U (X n) (Y n) (Z n) - X n - Y n) - 1)) atTop
      (𝓝 ((max (b + (y / x) * s + (x / y) * t) 0) ^ 2 / 4)) := by
  let f n := U (X n) (Y n) (Z n) - X n - Y n
  have h := shifted_threshold_limit hx hy hxy hk hX hY hZ
  have hf : Tendsto f atTop (𝓝 0) := by
    apply (h.div_atTop hk).congr'
    filter_upwards [hk.eventually_gt_atTop 0] with n hn
    exact mul_div_cancel_left₀ (f n) hn.ne'
  have hd := (continuousAt_dslope_same.mpr (Real.hasDerivAt_exp 0).differentiableAt).tendsto.comp hf
  have he (u : ℝ) : u * dslope Real.exp 0 u = Real.exp u - 1 := by
    simpa only [sub_zero, smul_eq_mul, Real.exp_zero] using sub_smul_dslope Real.exp 0 u
  simpa only [dslope_same, (Real.hasDerivAt_exp 0).deriv, Real.exp_zero, mul_one,
    Function.comp_apply, f, mul_assoc, he] using h.mul hd

noncomputable def trimmed (n : ℕ) (x s : ℝ) : ℕ := ⌈Real.exp (-s) * (n : ℝ) ^ x⌉₊

@[simp] theorem trimmed_zero (n : ℕ) (x : ℝ) : trimmed n x 0 = side n x := by
  simp [trimmed, side]

theorem trimmed_pos {n : ℕ} (hn : 0 < n) (x s : ℝ) : 0 < trimmed n x s :=
  Nat.ceil_pos.mpr (by positivity)

theorem trimmed_le (n : ℕ) (x : ℝ) (hs : 0 ≤ s) : trimmed n x s ≤ side n x := by
  apply Nat.ceil_mono
  exact mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs))

theorem log_trimmed (hx : 0 < x) (s : ℝ) :
    Tendsto (fun n : ℕ => Real.log (trimmed n x s) - x * Real.log n) atTop (𝓝 (-s)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) ^ x) atTop atTop :=
    (tendsto_rpow_atTop hx).comp tendsto_natCast_atTop_atTop
  have h := ((tendsto_nat_ceil_mul_div_atTop (Real.exp_pos (-s)).le).comp hn).log
    (Real.exp_ne_zero _)
  rw [Real.log_exp] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn'
  change Real.log ((trimmed n x s : ℝ) / (n : ℝ) ^ x) = _
  have hp := trimmed_pos hn' x s
  rw [Real.log_div (by positivity) (by positivity), Real.log_rpow (by positivity)]

theorem log_side (hx : 0 < x) :
    Tendsto (fun n : ℕ => Real.log (side n x) - x * Real.log n) atTop (𝓝 0) := by
  simpa only [trimmed_zero, neg_zero] using log_trimmed hx 0

theorem log_area (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) :
    Tendsto (fun n : ℕ => Real.log ((side n x : ℝ) * side n y) - Real.log n) atTop (𝓝 0) := by
  have h := (log_side hx).add (log_side hy)
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have h₁ := trimmed_pos hn x 0
  have h₂ := trimmed_pos hn y 0
  rw [trimmed_zero] at h₁ h₂
  rw [Real.log_mul (by positivity) (by positivity)]
  linear_combination -(Real.log n) * hxy

/-- Normalize by the untrimmed output area. This version allows arbitrary
sequences of logarithmic side lengths with the stipulated shifts. -/
theorem shifted_surplus_limit (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (hX : Tendsto (fun n => X n - x * Real.log n) atTop (𝓝 (-s)))
    (hY : Tendsto (fun n => Y n - y * Real.log n) atTop (𝓝 (-t)))
    (hZ : Tendsto (fun n => Z n - x * y * Real.log n) atTop (𝓝 (b * (x * y)))) :
    Tendsto (fun n => (Real.exp (U (X n) (Y n) (Z n)) - Real.exp (X n + Y n)) *
      Real.log ((side n x : ℝ) * side n y) / ((side n x : ℝ) * side n y)) atTop
      (𝓝 (Real.exp (-s - t) * (max (b + (y / x) * s + (x / y) * t) 0) ^ 2 / 4)) := by
  let D n := (side n x : ℝ) * side n y
  have hk : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hd := log_area hx hy hxy
  have hlog : Tendsto (fun n => Real.log (D n) / Real.log n) atTop (𝓝 1) :=
    side_ratio (x := 1) hk (by simpa only [one_mul] using hd)
  have he : Tendsto (fun n => X n + Y n - Real.log (D n)) atTop (𝓝 (-s - t)) := by
    have he' := (hX.add hY).sub hd
    rw [sub_zero, ← sub_eq_add_neg] at he'
    apply he'.congr'
    filter_upwards [] with n
    unfold D
    linear_combination -(Real.log n) * hxy
  have h := (he.rexp.mul (exp_shifted_threshold_limit hx hy hxy hk hX hY hZ)).mul hlog
  rw [mul_one, ← mul_div_assoc] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hk₀ : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hD : 0 < D n := by
    have hn' : 0 < n := by omega
    have h₁ := trimmed_pos hn' x 0
    have h₂ := trimmed_pos hn' y 0
    rw [trimmed_zero] at h₁ h₂
    unfold D
    positivity
  change _ = (Real.exp _ - Real.exp _) * Real.log (D n) / D n
  rw [Real.exp_sub, Real.exp_log hD, Real.exp_sub, Real.exp_sub, Real.exp_add]
  field_simp

theorem trimmed_shifted_surplus_limit (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    {inner : ℕ → ℕ} (hinner : Tendsto (fun n => Real.log (inner n) - x * y * Real.log n) atTop
      (𝓝 (b * (x * y)))) (s t : ℝ) :
    Tendsto (fun n : ℕ =>
      (Real.exp (U (Real.log (trimmed n x s)) (Real.log (trimmed n y t)) (Real.log (inner n))) -
        (trimmed n x s : ℝ) * trimmed n y t) *
      Real.log ((side n x : ℝ) * side n y) / ((side n x : ℝ) * side n y)) atTop
      (𝓝 (Real.exp (-s - t) * (max (b + (y / x) * s + (x / y) * t) 0) ^ 2 / 4)) := by
  apply (shifted_surplus_limit hx hy hxy (log_trimmed hx s) (log_trimmed hy t) hinner).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have h₁ := trimmed_pos hn x s
  have h₂ := trimmed_pos hn y t
  rw [Real.exp_add, Real.exp_log (by positivity), Real.exp_log (by positivity)]

theorem Threshold.log_width (hx : 0 < x) (hy : 0 < y) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => Real.log (Threshold.width n x y a) - x * y * Real.log n) atTop
      (𝓝 ((Real.log a / (x * y)) * (x * y))) := by
  rw [div_mul_cancel₀ _ (by positivity)]
  simpa only [trimmed, Threshold.width, neg_neg, Real.exp_log ha] using
    log_trimmed (mul_pos hx hy) (-Real.log a)

theorem threshold_limit (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hk : Tendsto k atTop atTop)
    (hX : Tendsto (fun n => X n - x * k n) atTop (𝓝 (-s)))
    (hY : Tendsto (fun n => Y n - y * k n) atTop (𝓝 (-t)))
    (hZ : Tendsto (fun n => Z n - x * y * k n) atTop (𝓝 0)) :
    Tendsto (fun n => k n * (U (X n) (Y n) (Z n) - X n - Y n)) atTop
      (𝓝 (((y / x) * s + (x / y) * t) ^ 2 / 4)) := by
  simpa only [zero_add, max_eq_left (by positivity : 0 ≤ (y / x) * s + (x / y) * t)] using
    shifted_threshold_limit (b := 0) hx hy hxy hk hX hY (by simpa using hZ)

theorem exp_threshold_limit (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hk : Tendsto k atTop atTop)
    (hX : Tendsto (fun n => X n - x * k n) atTop (𝓝 (-s)))
    (hY : Tendsto (fun n => Y n - y * k n) atTop (𝓝 (-t)))
    (hZ : Tendsto (fun n => Z n - x * y * k n) atTop (𝓝 0)) :
    Tendsto (fun n => k n * (Real.exp (U (X n) (Y n) (Z n) - X n - Y n) - 1)) atTop
      (𝓝 (((y / x) * s + (x / y) * t) ^ 2 / 4)) := by
  simpa only [zero_add, max_eq_left (by positivity : 0 ≤ (y / x) * s + (x / y) * t)] using
    exp_shifted_threshold_limit (b := 0) hx hy hxy hk hX hY (by simpa using hZ)

theorem surplus_limit (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hX : Tendsto (fun n => X n - x * Real.log n) atTop (𝓝 (-s)))
    (hY : Tendsto (fun n => Y n - y * Real.log n) atTop (𝓝 (-t)))
    (hZ : Tendsto (fun n => Z n - x * y * Real.log n) atTop (𝓝 0)) :
    Tendsto (fun n => (Real.exp (U (X n) (Y n) (Z n)) - Real.exp (X n + Y n)) *
      Real.log ((side n x : ℝ) * side n y) / ((side n x : ℝ) * side n y)) atTop
      (𝓝 (Real.exp (-s - t) * ((y / x) * s + (x / y) * t) ^ 2 / 4)) := by
  simpa only [zero_add, max_eq_left (by positivity : 0 ≤ (y / x) * s + (x / y) * t)] using
    shifted_surplus_limit (b := 0) hx hy hxy hX hY (by simpa using hZ)

theorem trimmed_surplus_limit (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ =>
      (Real.exp (U (Real.log (trimmed n x s)) (Real.log (trimmed n y t)) (Real.log (side n (x * y)))) -
        (trimmed n x s : ℝ) * trimmed n y t) *
      Real.log ((side n x : ℝ) * side n y) / ((side n x : ℝ) * side n y)) atTop
      (𝓝 (Real.exp (-s - t) * ((y / x) * s + (x / y) * t) ^ 2 / 4)) := by
  simpa only [zero_add, max_eq_left (by positivity : 0 ≤ (y / x) * s + (x / y) * t)] using
    trimmed_shifted_surplus_limit (b := 0) hx hy hxy (inner := fun n => side n (x * y)) (by simpa using log_side (mul_pos hx hy)) s t

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end
