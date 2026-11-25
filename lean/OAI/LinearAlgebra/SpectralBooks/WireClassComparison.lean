import OAI.LinearAlgebra.SpectralBooks.ClassComparison
import OAI.LinearAlgebra.SpectralBooks.ConcreteSpectrum

/-!
# Strict spectral comparison with a varying preferred wire

A spectral point may prefer a different pair at each point. The direct sum over
all pairs gives a single source class for strict comparison, before the power
and copy count are chosen.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators NNReal Classical

namespace SiteTensor

noncomputable section

universe v
variable {I F : Type*} [Fintype I] [Nonempty I] [Field F]
  {E : Type*} [Fintype E] [Nonempty E]

/-- If each normalized point prices one amplified candidate above the amplified target,
strict comparison produces a common copy count, uniform in every subsequent power. -/
theorem strict_comparison_of_log_power_cover
    (strict : StrictSpectralComparison.{v} I F)
    {X : TensorClass.{v} I F} (Y : E → TensorClass.{v} I F)
    (hX : X ≠ 0) (hY : ∀ e, Y e ≠ 0) (m : ℕ) (b : E → ℕ)
    (cover : ∀ φ : normalizedSpectrum (S := TensorClass.{v} I F) (· ≤ ·), ∃ e,
      (m : ℝ) * Real.logb 2 (φ.val X : ℝ) < b e * Real.logb 2 (φ.val (Y e) : ℝ)) :
    ∃ K : ℕ, 0 < K ∧ ∀ j : ℕ, 0 < j →
      (X ^ m) ^ j ≤ K • ((∑ e, Y e ^ b e) ^ j) := by
  classical
  have part (e : E) : Y e ^ b e ≤ ∑ t, Y t ^ b t := by
    rw [← Finset.sum_erase_add Finset.univ (fun t => Y t ^ b t) (Finset.mem_univ e)]
    simpa only [zero_add] using add_mono (zero_le_tensor _) (le_refl (Y e ^ b e))
  have hy : ∑ e, Y e ^ b e ≠ 0 := by
    let e := Classical.arbitrary E
    intro h
    exact (pow_ne_zero (b e) (hY e)) (le_antisymm ((part e).trans_eq h) (zero_le_tensor _))
  apply strict _ _ (pow_ne_zero _ hX) hy
  intro φ
  obtain ⟨e, he⟩ := cover φ
  apply lt_of_lt_of_le _ (φ.property.2.2.2.2 _ _ (part e))
  change (normalizedSpectrum.toRingHom φ) (X ^ m) < (normalizedSpectrum.toRingHom φ) (Y e ^ b e)
  rw [map_pow, map_pow]
  have hxpos : 0 < (φ.val X : ℝ) := by exact_mod_cast spectral_value_pos φ hX
  have hypos : 0 < (φ.val (Y e) : ℝ) := by exact_mod_cast spectral_value_pos φ (hY e)
  rw [← Real.logb_pow, ← Real.logb_pow] at he
  exact_mod_cast (Real.logb_lt_logb_iff (by norm_num : 1 < (2 : ℝ))
    (pow_pos hxpos m) (pow_pos hypos (b e))).mp he

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
