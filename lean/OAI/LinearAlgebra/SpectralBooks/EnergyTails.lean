import OAI.LinearAlgebra.SpectralBooks.EnergyStates

/-! # Exponential control of the two energy tails

Tilting the inverse temperature on either side of its central value bounds the
Boltzmann mass outside the energy interval from `q⁴ X²` to `X²`. Each tilted
bound has a smaller exponential growth rate than the central partition sum.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Real
open scoped Topology

/-- An exponential with a strictly smaller linear growth rate is eventually
bounded by any fixed positive fraction of the larger exponential. -/
theorem eventually_exp_le_exp_div_of_rate {F G : ℝ → ℝ} {c : ℝ} (hc : c < 0)
    (h : Tendsto (fun X ↦ (F X - G X) / X) atTop (𝓝 c)) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ X in atTop, exp (F X) ≤ exp (G X) / d := by
  have hz : Tendsto (fun X : ℝ ↦ -log d / X) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (-log d)
  filter_upwards [h.eventually_lt hz hc, eventually_gt_atTop (0 : ℝ)] with X hX hpos
  have hsub := (div_lt_div_iff_of_pos_right hpos).mp hX
  rw [← exp_log hd, ← exp_sub]
  exact exp_le_exp.mpr (by linarith)

/-- An eventual tail estimate for Boltzmann weights tilted from `k / X` to `t / X`. -/
private theorem eventually_fermion_tilt {A k t w : ℝ} (hk : 0 < k) (ht : 0 < t)
    (hF : ∀ k : ℝ, 0 < k →
      Tendsto (fun X : ℝ ↦ fermionLogPartition (k / X) / X) atTop (𝓝 (A / k)))
    (hgap : (t - k) * w + A / t - A / k < 0) :
    ∀ᶠ X : ℝ in atTop, exp ((t / X - k / X) * (w * X ^ 2) + fermionLogPartition (t / X)) ≤
      exp (fermionLogPartition (k / X)) / 4 := by
  apply eventually_exp_le_exp_div_of_rate hgap _ (by norm_num)
  refine (((hF t ht).const_add ((t - k) * w)).sub (hF k hk)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  field_simp

/-- Exponentially tilting the two tails leaves at least half of the central
partition sum in the interval from `q⁴ X²` to `X²`, for all sufficiently large `X`. -/
theorem eventually_fermion_tilt_tails {A q : ℝ} (hA : 0 < A)
    (hF : ∀ k : ℝ, 0 < k →
      Tendsto (fun X : ℝ ↦ fermionLogPartition (k / X) / X) atTop (𝓝 (A / k)))
    (hq : 0 < q) (hq1 : q < 1) :
    let k := sqrt A / q
    let a := q * k
    let b := k / q
    ∀ᶠ X : ℝ in atTop, 0 < X ∧
      exp ((b / X - k / X) * (q ^ 4 * X ^ 2) + fermionLogPartition (b / X)) ≤
        exp (fermionLogPartition (k / X)) / 4 ∧
      exp ((a / X - k / X) * X ^ 2 + fermionLogPartition (a / X)) ≤
        exp (fermionLogPartition (k / X)) / 4 := by
  dsimp only
  let k := sqrt A / q
  have hk : 0 < k := div_pos (sqrt_pos.mpr hA) hq
  have hAk : A = (q * k) ^ 2 := by
    rw [show q * k = sqrt A by dsimp [k]; field_simp, sq_sqrt hA.le]
  have gap₁ : (k / q - k) * q ^ 4 + A / (k / q) - A / k < 0 := by
    rw [show (k / q - k) * q ^ 4 + A / (k / q) - A / k = -(1 - q) ^ 2 * k * q ^ 2 by
      rw [hAk]; field_simp; ring]
    have hp : 0 < (1 - q) ^ 2 * k * q ^ 2 := by positivity
    linarith
  have gap₂ : (q * k - k) * 1 + A / (q * k) - A / k < 0 := by
    rw [show (q * k - k) * 1 + A / (q * k) - A / k = -(1 - q) ^ 2 * k by
      rw [hAk]; field_simp; ring]
    have hp : 0 < (1 - q) ^ 2 * k := by positivity
    linarith
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_fermion_tilt hk (div_pos hk hq) hF gap₁,
    eventually_fermion_tilt hk (mul_pos hq hk) hF gap₂] with X hX h₁ h₂
  exact ⟨hX, h₁, by simpa only [one_mul] using h₂⟩

end SpectralBooks
end LinearAlgebra
end OAI
