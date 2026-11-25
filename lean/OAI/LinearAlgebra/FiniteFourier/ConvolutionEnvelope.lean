import OAI.LinearAlgebra.FiniteFourier.ConvolutionRecurrence
import OAI.LinearAlgebra.FiniteFourier.ConvolutionCost

/-! # The shorter-length envelope in the integral convolution bound -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter

/-- Scalar operation count per input coefficient of the smallest integral
multiplication circuit. -/
noncomputable def convolutionRate (n : ℕ) : ℝ := (integralConvolutionCost n : ℝ) / n

/-- The envelope `1 + max_{1≤j≤s} D(j)/j` from the cost recurrence. -/
noncomputable def convolutionEnvelope (s : ℕ) : ℝ :=
  if h : 0 < s then 1 + (Finset.Icc 1 s).sup' ⟨s, Finset.mem_Icc.mpr ⟨h, le_rfl⟩⟩ convolutionRate
  else 1

theorem convolutionRate_nonneg (n : ℕ) : 0 ≤ convolutionRate n := by unfold convolutionRate; positivity

theorem exists_convolutionEnvelope_eq {s : ℕ} (hs : 0 < s) :
    ∃ j ∈ Finset.Icc 1 s, convolutionEnvelope s = 1 + convolutionRate j := by
  let S := Finset.Icc 1 s
  have hS : S.Nonempty := ⟨s, Finset.mem_Icc.mpr ⟨hs, le_rfl⟩⟩
  obtain ⟨j, hj, hm⟩ := S.exists_max_image convolutionRate hS
  refine ⟨j, hj, ?_⟩
  simp only [convolutionEnvelope, dite_eq_left hs]
  congr 1
  exact le_antisymm (Finset.sup'_le _ _ hm) (Finset.le_sup' convolutionRate hj)

theorem convolutionEnvelope_one_le {s : ℕ} (hs : 0 < s) : 1 ≤ convolutionEnvelope s := by
  obtain ⟨j, -, hj⟩ := exists_convolutionEnvelope_eq hs
  rw [hj]
  exact le_add_of_nonneg_right (convolutionRate_nonneg _)

theorem convolutionRate_le_envelope {s j : ℕ} (hj : 0 < j) (hjs : j ≤ s) :
    convolutionRate j ≤ convolutionEnvelope s := by
  simp only [convolutionEnvelope, dite_eq_left (hj.trans_le hjs)]
  exact (Finset.le_sup' convolutionRate (Finset.mem_Icc.mpr ⟨hj, hjs⟩)).trans (by linarith)

private theorem eventually_gauge_le_logb {β α : ℝ} (hβ : 0 < β) (hβα : β < α) :
    ∀ᶠ n : ℕ in atTop, convolutionGauge β (Real.log n) ≤ (1 + Real.logb 2 n)^α := by
  have htop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow := htop.eventually ((isLittleO_log_rpow_rpow_atTop (2-β) (sub_pos.mpr hβα)).bound
    (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hpow, htop.eventually_ge_atTop 3] with n hp hn
  change 3 ≤ Real.log (n : ℝ) at hn
  let T := Real.log (n : ℝ)
  have hT : 0 < T := by dsimp only [T]; linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by dsimp [T]; linarith)
  have hle : (Real.log T)^(2-β) ≤ T^(α-β) := by
    change ‖(Real.log T)^(2-β)‖ ≤ 1 * ‖T^(α-β)‖ at hp
    simpa only [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
      Real.norm_of_nonneg (Real.rpow_nonneg hT.le _)] using hp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hbase : T ≤ Real.logb 2 n := (le_div_iff₀ hlog2).2 (mul_le_of_le_one_right hT.le hlog2')
  change convolutionGauge β T ≤ _
  rw [convolutionGauge, max_eq_right hn]
  calc
    _ ≤ T^β * T^(α-β) := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hT.le _)
    _ = T^α := by rw [← Real.rpow_add hT]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow hT.le (by linarith) (hβ.trans hβα).le

/-- The closed recurrence for least actual program sizes implies the stated
integral circuit bound for every target exponent strictly above `β`. -/
theorem integralConvolutionBound_of_recurrence {β α σ C : ℝ} (hβ : 0 < β) (hβ' : β ≤ 1)
    (hβα : β < α) (hσ : 0 < σ) (hσ' : σ < 1) (hC : 0 < C)
    (hrec : ∀ᶠ n : ℕ in atTop, ∃ s : ℕ, 0 < s ∧ Real.log s ≤ (Real.log n)^σ ∧
      convolutionRate n ≤ C * (convolutionGauge β (Real.log n) +
          (Real.log (Real.log n))^3 * convolutionEnvelope s)) :
    ∃ K > (0 : ℝ), IntegralConvolutionBound α K := by
  obtain ⟨A, hA, hall⟩ := convolution_recurrence_bound (f := convolutionRate) hβ hβ' hσ hσ' hC
    (by
      filter_upwards [hrec] with n hn
      obtain ⟨s, hs, hshort, hcost⟩ := hn
      obtain ⟨j, hj, he⟩ := exists_convolutionEnvelope_eq hs
      have hm := Finset.mem_Icc.mp hj
      rw [he] at hcost
      exact ⟨j, hm.1, (Real.log_le_log (by exact_mod_cast hm.1 : 0 < (j : ℝ))
        (by exact_mod_cast hm.2)).trans hshort, hcost⟩)
  obtain ⟨n₀, hlarge⟩ := eventually_atTop.mp (eventually_gauge_le_logb hβ hβα)
  let B := A + ∑ j ∈ Finset.range n₀, convolutionRate j
  have htail : 0 ≤ ∑ j ∈ Finset.range n₀, convolutionRate j := Finset.sum_nonneg fun i _ => convolutionRate_nonneg i
  have hB : A ≤ B := le_add_of_nonneg_right htail
  refine ⟨B, hA.trans_le hB, integralConvolutionBound_iff.2 ?_⟩
  intro n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hone : 1 ≤ (1 + Real.logb 2 n)^α := Real.one_le_rpow (by
    linarith [Real.logb_nonneg (by norm_num : (1:ℝ)<2) (by exact_mod_cast hn : 1 ≤ (n:ℝ))]) (hβ.trans hβα).le
  have hrate : convolutionRate n ≤ B*(1+Real.logb 2 n)^α := by
    by_cases h : n < n₀
    · have hsum := Finset.single_le_sum (fun j _ => convolutionRate_nonneg j) (Finset.mem_range.mpr h)
      have hs : convolutionRate n ≤ B := hsum.trans (by dsimp [B]; linarith)
      exact hs.trans (le_mul_of_one_le_right (hA.trans_le hB).le hone)
    · exact (hall n).trans (mul_le_mul hB (hlarge n (by omega))
        (by linarith [convolutionGauge_one_le hβ.le hβ' (Real.log n)]) (hA.trans_le hB).le)
  have hfinal := (div_le_iff₀ hn').1 hrate
  linarith only [hfinal]

end FiniteFourier
end LinearAlgebra
end OAI
