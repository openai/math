import OAI.LinearAlgebra.SpectralBooks.ChiRadius
import OAI.LinearAlgebra.SpectralBooks.NormalTail

/-! # Student upper tail as a Gaussian scale mixture

Conditioning on the independent chi radius of the denominator expresses the
Student upper tail as an average of standard normal upper tails.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open MeasureTheory

section

/-- The upper tail for `d` degrees of freedom, obtained by conditioning the
Student ratio on its chi-distributed denominator. -/
def studentTail (d : ℕ) (s : ℝ) : ℝ :=
  ∫ h : ℝ, chiDensity d h * normalTail (s / Real.sqrt d * h)

private lemma norm_chiDensity_mul_normalTail_le {d : ℕ} (hd : 0 < d) (k h : ℝ) :
    ‖chiDensity d h * normalTail (k * h)‖ ≤ chiDensity d h := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (chiDensity_nonneg hd h) (normalTail_nonneg _))]
  exact mul_le_of_le_one_right (chiDensity_nonneg hd h) (normalTail_le_one _)

lemma integrable_chiDensity_mul_normalTail {d : ℕ} (hd : 0 < d) (k : ℝ) :
    Integrable (fun h ↦ chiDensity d h * normalTail (k * h)) := by
  apply (integrable_chiDensity hd).mono'
  · exact ((measurable_chiDensity d).mul
      (normalTail_continuous.measurable.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  · exact ae_of_all _ (norm_chiDensity_mul_normalTail_le hd k)

theorem studentTail_continuous {d : ℕ} (hd : 0 < d) : Continuous (studentTail d) := by
  unfold studentTail
  apply continuous_of_dominated (bound := chiDensity d)
  · exact fun s ↦ (integrable_chiDensity_mul_normalTail hd (s / Real.sqrt d)).aestronglyMeasurable
  · exact fun s ↦ ae_of_all _ (norm_chiDensity_mul_normalTail_le hd (s / Real.sqrt d))
  · exact integrable_chiDensity hd
  · exact ae_of_all _ fun h ↦ continuous_const.mul
      (normalTail_continuous.comp ((continuous_id.div_const _).mul continuous_const))

theorem studentTail_nonneg (d : ℕ) (s : ℝ) : 0 ≤ studentTail d s := by
  rcases d.eq_zero_or_pos with rfl | hd
  · simp [studentTail, chiDensity, chiNormalizer]
  · exact integral_nonneg fun h ↦ mul_nonneg (chiDensity_nonneg hd h) (normalTail_nonneg _)

theorem studentTail_le_one {d : ℕ} (hd : 0 < d) (s : ℝ) : studentTail d s ≤ 1 := by
  rw [← integral_chiDensity hd]
  exact integral_mono (integrable_chiDensity_mul_normalTail hd (s / Real.sqrt d))
    (integrable_chiDensity hd) fun h ↦ mul_le_of_le_one_right (chiDensity_nonneg hd h) (normalTail_le_one _)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
