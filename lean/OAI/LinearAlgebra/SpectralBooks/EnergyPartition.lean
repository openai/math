import OAI.LinearAlgebra.SpectralBooks.EnergyStates
import Mathlib.Analysis.SumIntegralComparisons

/-! # The free-energy limit of the fermionic partition function

The midpoint sum on modes of energy `i + 1/2` lies between the left and right sums
for a decreasing integrable profile. Their difference is its first summand.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open MeasureTheory Real Set Filter Topology

/-- Free energy contributed by a single mode at scaled energy `x`. -/
def fermionProfile (x : ℝ) : ℝ := log (1 + exp (-x))

/-- The coefficient of the reciprocal inverse temperature in the log partition function. -/
def fermionFreeEnergy : ℝ := ∫ x in Ioi (0 : ℝ), fermionProfile x

theorem fermionProfile_pos (x : ℝ) : 0 < fermionProfile x :=
  log_pos (by simpa using exp_pos (-x))

private theorem antitone_fermionProfile : Antitone fermionProfile := by
  intro x y hxy
  exact log_le_log (by positivity) (add_le_add_right (exp_le_exp.mpr (neg_le_neg hxy)) 1)

private theorem summable_profile_nat {a : ℝ} (ha : 0 < a) :
    Summable (fun i : ℕ ↦ fermionProfile (a * i)) := by
  simpa only [fermionProfile, neg_mul] using Real.summable_log_one_add_of_summable
    (Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr ha) (fun i : ℕ ↦ le_refl (i : ℝ)))

private theorem integrable_profile_scaled {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ fermionProfile (a * x)) (Ioi 0) :=
  (antitone_fermionProfile.comp_monotone (fun _ _ h ↦ mul_le_mul_of_nonneg_left h ha.le)).antitoneOn (Ici 0)
    |>.integrableOn_Ioi_zero_of_summable (summable_profile_nat ha) (fun x _ ↦ (fermionProfile_pos (a * x)).le)

theorem fermionFreeEnergy_pos : 0 < fermionFreeEnergy := by
  have hi : IntegrableOn fermionProfile (Ioi 0) := by
    simpa using integrable_profile_scaled zero_lt_one
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun x ↦ (fermionProfile_pos x).le) hi).mpr
  have hs : Function.support fermionProfile = univ :=
    Set.eq_univ_of_forall fun x ↦ (fermionProfile_pos x).ne'
  rw [hs, univ_inter]
  exact isOpen_Ioi.measure_pos volume nonempty_Ioi

/-- Upper and lower integral-test errors for the scaled midpoint sum. -/
theorem fermionLogPartition_integral_bounds {a : ℝ} (ha : 0 < a) :
    fermionFreeEnergy - a * fermionProfile 0 ≤ a * fermionLogPartition a ∧
    a * fermionLogPartition a ≤ fermionFreeEnergy + a * fermionProfile 0 := by
  let F (x : ℝ) := fermionProfile (a * x)
  have anti : Antitone F := antitone_fermionProfile.comp_monotone
    (fun _ _ h ↦ mul_le_mul_of_nonneg_left h ha.le)
  have nonneg (x : ℝ) : 0 ≤ F x := (fermionProfile_pos _).le
  have hs : Summable (fun i : ℕ ↦ F i) := summable_profile_nat ha
  have hm : Summable (fun i : ℕ ↦ F (i + 1 / 2)) :=
    hs.of_nonneg_of_le (fun i ↦ nonneg _) (fun i ↦ anti (by linarith))
  have hl : ∑' i : ℕ, F (i + 1 / 2) ≤ ∑' i : ℕ, F i :=
    hm.tsum_le_tsum (fun i ↦ anti (by linarith)) hs
  have hr : ∑' i : ℕ, F (i + 1 : ℕ) ≤ ∑' i : ℕ, F (i + 1 / 2) :=
    (summable_nat_add_iff 1 |>.mpr hs).tsum_le_tsum (fun i ↦ anti (by push_cast; linarith)) hm
  have h₁ := (anti.antitoneOn (Ici 0)).tsum_le_integral (integrable_profile_scaled ha) (fun x _ ↦ nonneg x)
  have h₂ := (anti.antitoneOn (Ici 0)).integral_le_tsum hs (fun x _ ↦ nonneg x)
  have heq := hs.tsum_eq_zero_add
  have hi : a * (∫ x in Ioi 0, F x) = fermionFreeEnergy := by
    simpa only [F, smul_eq_mul, mul_zero, fermionFreeEnergy] using
      integral_comp_mul_left_Ioi' fermionProfile 0 ha
  have hmEq : (∑' i : ℕ, F (i + 1 / 2)) = fermionLogPartition a := by
    simp only [F, fermionProfile, fermionLogPartition, neg_mul]
  have hF : F 0 = fermionProfile 0 := by simp [F]
  rw [← hmEq, ← hi, ← hF]
  constructor
  · rw [← mul_sub]
    apply mul_le_mul_of_nonneg_left _ ha.le
    change (∑' i : ℕ, F (i : ℝ)) = F (0 : ℕ) + ∑' i : ℕ, F (i + 1 : ℕ) at heq
    norm_cast at heq
    linarith
  · rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ ha.le
    linarith

/-- The half-integer mode sum has limiting integral as the inverse temperature tends to zero. -/
theorem tendsto_fermionFreeEnergy :
    Tendsto (fun a : ℝ ↦ a * fermionLogPartition a) (𝓝[>] 0) (𝓝 fermionFreeEnergy) := by
  have h0 : Tendsto (fun a : ℝ ↦ a * fermionProfile 0) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).mul_const
      (fermionProfile 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using h0.const_sub fermionFreeEnergy) (by simpa using h0.const_add fermionFreeEnergy)
  · filter_upwards [self_mem_nhdsWithin] with a ha using (fermionLogPartition_integral_bounds ha).1
  · filter_upwards [self_mem_nhdsWithin] with a ha using (fermionLogPartition_integral_bounds ha).2

end

end

end SpectralBooks
end LinearAlgebra
end OAI
