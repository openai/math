import OAI.LinearAlgebra.SpectralBooks.EnergyAsymptotic
import OAI.LinearAlgebra.SpectralBooks.EnergyPartition
import OAI.LinearAlgebra.SpectralBooks.EnergyTails
import OAI.LinearAlgebra.SpectralBooks.EnergyWindow

/-! # Asymptotic count of fermionic states

The free energy controls the upper bound on the count directly. Two nearby
inverse temperatures bound the Boltzmann weight in both tails, giving the
matching lower exponential rate.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Real
open scoped Topology

private theorem tendsto_fermionLogPartition_scaled (k : ℝ) (hk : 0 < k) :
    Tendsto (fun X : ℝ ↦ fermionLogPartition (k / X) / X) atTop (𝓝 (fermionFreeEnergy / k)) := by
  have ht : Tendsto (fun X : ℝ ↦ k / X) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.const_div_atTop k, (eventually_gt_atTop (0 : ℝ)).mono
      (fun _ hx ↦ div_pos hk hx)⟩
  refine ((tendsto_fermionFreeEnergy.comp ht).div_const k).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hx
  dsimp only [Function.comp_apply]
  field_simp

private theorem eventually_fermionCount_sqrt_lower (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    ∀ᶠ X : ℝ in atTop, fermionLogPartition ((√fermionFreeEnergy / q) / X) +
      (√fermionFreeEnergy * q ^ 3) * X - log 2 ≤ log (fermionCount (X ^ 2)) := by
  let k := √fermionFreeEnergy / q
  let a := q * k
  let b := k / q
  have hk : 0 < k := div_pos (sqrt_pos.mpr fermionFreeEnergy_pos) hq
  have ha : 0 < a := mul_pos hq hk
  have haw : a < k := by dsimp [a]; nlinarith [mul_pos (sub_pos.mpr hq1) hk]
  have hwb : k < b := (lt_div_iff₀ hq).mpr (by simpa [mul_comm] using haw)
  filter_upwards [eventually_fermion_tilt_tails fermionFreeEnergy_pos
    tendsto_fermionLogPartition_scaled hq hq1] with X ⟨hX, hlow, hhigh⟩
  have hwindow := fermionPartition_le_window (div_pos ha hX)
    ((div_lt_div_iff_of_pos_right hX).mpr haw) ((div_lt_div_iff_of_pos_right hX).mpr hwb)
    (q ^ 4 * X ^ 2) (X ^ 2)
  have half : exp (fermionLogPartition (k / X)) / 2 ≤
      (fermionCount (X ^ 2) : ℝ) * exp (-(k / X) * (q ^ 4 * X ^ 2)) := by
    linarith only [hwindow, hlow, hhigh]
  have key : -(k / X) * (q ^ 4 * X ^ 2) = -((√fermionFreeEnergy * q ^ 3) * X) := by
    dsimp [k]
    field_simp
  rw [key, exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)] at half
  rw [le_log_iff_exp_le (by exact_mod_cast fermionCount_pos (sq_nonneg X)), exp_sub, exp_add,
    exp_log (by norm_num : (0 : ℝ) < 2)]
  linarith only [half]

/-- The natural logarithm of the state count divided by the square root of the energy. -/
theorem tendsto_log_fermionCount_div_sqrt :
    Tendsto (fun H : ℝ ↦ log (fermionCount H) / √H) atTop (𝓝 (2 * √fermionFreeEnergy)) :=
  tendsto_log_fermionCount_div_sqrt_of_partition fermionFreeEnergy_pos
    tendsto_fermionLogPartition_scaled eventually_fermionCount_sqrt_lower

/-- The manuscript's constant in `log₂ D(H) ∼ c √H`. -/
theorem tendsto_logb_fermionCount_div_sqrt :
    Tendsto (fun H : ℝ ↦ logb 2 (fermionCount H) / √H) atTop
      (𝓝 (2 * √fermionFreeEnergy / log 2)) :=
  tendsto_logb_fermionCount_div_sqrt_of_log tendsto_log_fermionCount_div_sqrt

end SpectralBooks
end LinearAlgebra
end OAI
