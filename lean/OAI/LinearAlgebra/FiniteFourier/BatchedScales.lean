import Mathlib.Tactic

/-! # Uniform thin-rectangle parameters -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier
noncomputable section

def batchHeight (m : ℝ) := (16/5) / Real.sqrt m
def batchTriangle (L : ℝ) := (L + Real.sqrt (L^2 + 1)) / 2
def batchHubTriangle (L : ℝ) := L/2 + Real.sqrt (1/16 + L^2/4)

structure BatchScaleBounds (m L δ τ : ℝ) : Prop where
  height_pos : 0 < L
  height_le : L ≤ 1/100
  half_le : 1/2 ≤ δ
  triangle_le : δ ≤ 1
  ratio : δ / (L+1) ≤ 51/100
  gap : 5 * (L+1) ≤ (2*δ - (L+1)) * m
  hub_le : τ ≤ 1
  excess : (τ + 1/4 - δ) * m ≤ 11

theorem batch_scale_bounds {m : ℝ} (hm : 1000 ≤ Real.sqrt m) :
    BatchScaleBounds m (batchHeight m) (batchTriangle (batchHeight m))
      (batchHubTriangle (batchHeight m)) := by
  have hs : 0 < Real.sqrt m := by linarith
  have hmpos := Real.sqrt_pos.mp hs
  let L := batchHeight m
  let d := Real.sqrt (L^2+1)
  let h := Real.sqrt (1/16 + L^2/4)
  have hL : 0 < L := by unfold L batchHeight; positivity
  have hL' : L ≤ 1/100 := (div_le_iff₀ hs).mpr (by linarith)
  have hLm : L^2 * m = 256/25 := by
    unfold L batchHeight
    rw [div_pow, Real.sq_sqrt hmpos.le, div_mul_cancel₀ _ hmpos.ne']
    norm_num
  have hd2 : d^2 = L^2 + 1 := Real.sq_sqrt (by positivity)
  have hdpos : 0 ≤ d := Real.sqrt_nonneg _
  have hd : 1 ≤ d := by nlinarith
  have hd' : d ≤ 101/100 := by nlinarith
  have hg : 5 * (L+1) ≤ (d-1)*m := by
    have he : (d-1)*m*(d+1) = 256/25 := by
      calc
        _ = (d^2-1)*m := by ring
        _ = _ := by rw [hd2]; nlinarith
    apply le_of_mul_le_mul_right _ (show 0 < d+1 by linarith)
    rw [he]
    nlinarith
  have hh : h ≤ 1/4 + L^2/2 := by
    have hh2 : h^2 = 1/16 + L^2/4 := Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (L^2)]
  change BatchScaleBounds m L ((L+d)/2) (L/2+h)
  refine ⟨hL, hL', by linarith, by linarith, (div_le_iff₀ (by positivity)).mpr (by linarith),
    by nlinarith, by nlinarith, ?_⟩
  have he : L/2+h+1/4-(L+d)/2 ≤ L^2/2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right he hmpos.le]

theorem batch_dictionary_exponent {m : ℝ} (hm : 1000 ≤ Real.sqrt m) :
    ((2:ℝ) ^ (Real.sqrt m / 8)) ^
      (batchHeight m / batchTriangle (batchHeight m)) ≤ 179/100 := by
  have hs : 0 < Real.sqrt m := by linarith
  have hd := (batch_scale_bounds hm).half_le
  have hdpos : 0 < batchTriangle (batchHeight m) := by linarith
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply le_trans (b := (2:ℝ) ^ (4/5 : ℝ))
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hdpos).mpr
    have he : Real.sqrt m / 8 * batchHeight m = 2/5 := by
      unfold batchHeight
      field_simp
      ring
    linarith
  · apply le_of_pow_le_pow_left₀ (by decide : (5:ℕ) ≠ 0) (by norm_num : (0:ℝ) ≤ 179/100)
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
    norm_num

end
end FiniteFourier
end LinearAlgebra
end OAI
