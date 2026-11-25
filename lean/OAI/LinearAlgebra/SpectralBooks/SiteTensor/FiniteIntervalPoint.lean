import OAI.LinearAlgebra.SpectralBooks.IntervalPlacement
import OAI.LinearAlgebra.SpectralBooks.IntervalWireBounds

/-!
# An interval point preserving every old tensor evaluation

For an arbitrary field, a point in the spectrum on a finite party set extends
to one more party with prescribed distances to two old sites. The specified
nonnegative distances may be any two numbers whose sum is the old distance.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped NNReal
noncomputable section
namespace SiteTensor

variable {I : Type} {K : Type*} [Fintype I] [Nonempty I] [Field K]

/-- The normalized spectral point on the enlarged site set preserves all old
tensor prices and realizes the prescribed split of a binary wire's price. -/
theorem exists_spectral_interval_point
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
    (a b : I) (la lb : ℝ) (ha : 0 ≤ la) (hb : 0 ≤ lb)
    (hs : la + lb = rawWireDistance φ 1 a b) :
    ∃ ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) K → _ → Prop),
      (∀ T : Raw.{0} I K, rawLogPrice ψ 1 (T.group some) = rawLogPrice φ 1 T) ∧
      rawWireDistance ψ 1 none (some a) = la ∧ rawWireDistance ψ 1 none (some b) = lb := by
  obtain ⟨ψ, hψ, hA, hB⟩ := spectral_interval_of_wire_bounds φ
    (intervalWire K a) (intervalWire K b) la lb ha hb
    (fun m n ↦ by rw [hs]; exact contractionPrice_intervalWires_le φ a b m n)
    (fun m ↦ by rw [hs, contractionPrice_intervalWires_equal])
  exact ⟨ψ, group_some_logPrice_of_old_logPoint φ ψ hψ,
    (logPoint_intervalWire_eq ψ a).symm.trans hA, (logPoint_intervalWire_eq ψ b).symm.trans hB⟩

/-- Midpoint form of finite spectral interpolation, also for coinciding endpoints. -/
theorem exists_midpoint_spectral_point
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)) (a b : I) :
    ∃ ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) K → _ → Prop),
      (∀ T : Raw.{0} I K, rawLogPrice ψ 1 (T.group some) = rawLogPrice φ 1 T) ∧
      rawWireDistance ψ 1 none (some a) = rawWireDistance φ 1 a b / 2 ∧
      rawWireDistance ψ 1 none (some b) = rawWireDistance φ 1 a b / 2 := by
  have h : 0 ≤ rawWireDistance φ 1 a b := rawLogPrice_nonneg φ zero_le_one _
  exact exists_spectral_interval_point φ a b _ _ (by positivity) (by positivity) (by ring)

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
