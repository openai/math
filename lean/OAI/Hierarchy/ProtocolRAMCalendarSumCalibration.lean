import OAI.Hierarchy.ProtocolRAMAttemptThresholds

namespace OAI
/-! # Rounded words, threshold slack and the true sum of a native price check -/
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AttemptGate
open scoped BigOperators
noncomputable section
variable {w : ℕ}

/-- A row calibration contains one true scalar per individual rounded word. The
threshold slack reserves the sum of all rounding errors; no measured budget or
decision appears in these hypotheses. -/
structure SumCalibration (z : Check) (m : Memory w) (total cap : ℝ) where
  precision : ℕ
  value : Fin z.rows → ℝ
  threshold : ℝ
  positive : 0<precision
  value_nonneg : ∀ i, 0≤value i
  threshold_nonneg : 0≤threshold
  bound : z.bound = ⌈(precision:ℝ)*threshold⌉₊
  words : ∀ i, z.score m i = ⌊(precision:ℝ)*value i⌋₊
  sum_eq : ∑ i,value i = total
  room : threshold+(z.rows:ℝ)/precision≤cap

theorem SumCalibration.low {z : Check} {m : Memory w} {total cap : ℝ}
    (R : SumCalibration z m total cap) (quiet : z.high m=false) : total≤cap := by
  have small := (threshold_bounds R.value R.value_nonneg R.precision R.positive R.threshold R.threshold_nonneg).2
  have below : ¬ z.bound≤∑i,z.score m i := of_decide_eq_false quiet
  rw [R.bound] at below
  simp only [R.words] at below
  simpa only [R.sum_eq] using (small below).trans R.room

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
