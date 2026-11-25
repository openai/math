import OAI.LinearAlgebra.FiniteFourier.ConvolutionSmoothPacking

/-! # The power cutoff for the two disjoint prime lists

Taking the ceiling of `T ^ (1 + η / 3)` supplies enough primes while
preserving the short-operand and volume bounds in the transfer estimate.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Real Filter
open scoped Topology

/-- The cutoff for the disjoint-list construction at input logarithm `T`. -/
def dyadicPackingCutoff (η T : ℝ) : ℕ := ⌈T ^ (1 + η / 3)⌉₊

theorem tendsto_dyadicPackingCutoff {η : ℝ} (hη : 0 < η) :
    Tendsto (fun T ↦ (dyadicPackingCutoff η T : ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun T ↦ Nat.le_ceil (T ^ (1 + η / 3)))
    (tendsto_rpow_atTop (by linarith : 0 < 1 + η / 3))

/-- Both costs of the common order at the power cutoff. The logarithmic
slack absorbs the factor of `log B` in the prime-power product. -/
theorem eventually_dyadicPackingCutoff_bounds {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 4) :
    ∀ᶠ T : ℝ in atTop, let B : ℝ := dyadicPackingCutoff η T
      log (6 * (smoothRootOrder B η : ℝ) * (8*B^2+1)) ≤ T ^ (1-η/2) ∧
      (smoothRootOrder B η : ℝ) * B^2 ≤ exp T := by
  have hlog := (isLittleO_log_rpow_atTop (show 0 < η/6 by positivity)).bound
    (by norm_num : (0 : ℝ) < 1/18)
  filter_upwards [hlog, eventually_ge_atTop (16 : ℝ)] with T hl hT
  let B : ℝ := dyadicPackingCutoff η T
  change log (6 * (smoothRootOrder B η : ℝ) * (8*B^2+1)) ≤ _ ∧ _ * B^2 ≤ _
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hin : 1 ≤ T ^ (1 + η / 3) := one_le_rpow hT1 (by linarith)
  have hB : 1 ≤ B := hin.trans (Nat.le_ceil _)
  have hBlarge : B ≤ 2 * T ^ (1+η/3) := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ T ^ (1+η/3))
    change (⌈T ^ (1+η/3)⌉₊ : ℝ) ≤ _
    linarith
  have hBpoly : B ≤ 2*T^2 := by
    refine hBlarge.trans ?_
    rw [← Real.rpow_natCast T 2]
    gcongr
    norm_num
    linarith
  have hlogB : log (8*B) ≤ 3*log T := by
    rw [show (3 : ℝ)*log T = log (T^3) by rw [log_pow]; norm_num]
    apply log_le_log (by positivity : 0 < 8*B)
    nlinarith only [hBpoly, mul_nonneg (sub_nonneg.mpr hT) (sq_nonneg T)]
  have hβ : 0 ≤ 1-η := by linarith
  have hpow : B^(1-η) ≤ 2 * T^((1+η/3)*(1-η)) := by
    calc
      _ ≤ (2 * T^(1+η/3))^(1-η) := Real.rpow_le_rpow (by positivity) hBlarge hβ
      _ = (2:ℝ)^(1-η) * T^((1+η/3)*(1-η)) := by
        rw [mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity), rpow_mul hTp.le]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (rpow_nonneg hTp.le _)
        simpa using rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          (by linarith : 1-η ≤ 1)
  change ‖log T‖ ≤ (1/18 : ℝ)*‖T^(η/6)‖ at hl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (log_nonneg hT1),
    abs_of_nonneg (rpow_nonneg hTp.le _)] at hl
  have hshort : log (6 * (smoothRootOrder B η : ℝ) * (8*B^2+1)) ≤ T ^ (1-η/2) := by
    calc
      _ ≤ 3 * B^(1-η) * log (8*B) := log_smoothRootOrder_jet_le hB (by linarith)
      _ ≤ 3 * (2 * T^((1+η/3)*(1-η))) * (3*log T) := by
        gcongr
        exact log_nonneg (by linarith)
      _ = T^((1+η/3)*(1-η)) * (18*log T) := by ring
      _ ≤ T^((1+η/3)*(1-η)) * T^(η/6) :=
        mul_le_mul_of_nonneg_left (by linarith) (rpow_nonneg hTp.le _)
      _ ≤ _ := by
        rw [← rpow_add hTp]
        exact rpow_le_rpow_of_exponent_le hT1 (by nlinarith [sq_nonneg η])
  refine ⟨hshort, ?_⟩
  have hM : (0:ℝ) < smoothRootOrder B η := by exact_mod_cast smoothRootOrder_pos B η
  apply (log_le_iff_le_exp (by positivity)).mp
  calc
    _ ≤ log (6 * (smoothRootOrder B η : ℝ) * (8*B^2+1)) := by
      apply log_le_log (by positivity)
      nlinarith only [mul_nonneg hM.le (sq_nonneg B), hM.le]
    _ ≤ T ^ (1-η/2) := hshort
    _ ≤ T := (rpow_le_rpow_of_exponent_le hT1 (by linarith : 1-η/2 ≤ 1)).trans_eq (rpow_one T)

end

end

end FiniteFourier
end LinearAlgebra
end OAI
