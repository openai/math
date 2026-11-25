import OAI.LinearAlgebra.SpectralBooks.GroupedPower
import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import OAI.LinearAlgebra.SpectralBooks.ScalarRestriction
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Spectral evaluation on finite linear spans and tensor powers

A scalar coefficient can be absorbed at one site. Thus a linear combination
has spectral value at most the sum of the spectral values of its generators,
independently of the field coefficients. Powers evaluate multiplicatively.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v

open scoped NNReal

variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
  {A : I → Type v} [∀ i, Fintype (A i)]
  (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))

theorem coeffValue_smul_le (c : K) (T : (∀ i, A i) → K) :
    coeffValue φ (c • T) ≤ coeffValue φ T :=
  φ.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr (scalar_mul_restricts c T))

/-- The number of generators controls the spectral cost of any point in their span. -/
theorem coeffValue_span_le {J : Type*} [Fintype J] (U : J → (∀ i, A i) → K)
    {T : (∀ i, A i) → K} (hT : T ∈ Submodule.span K (Set.range U))
    {B : ℝ≥0} (hB : ∀ j, coeffValue φ (U j) ≤ B) :
    coeffValue φ T ≤ Fintype.card J * B := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hT
  calc
    _ ≤ ∑ j, coeffValue φ (c j • U j) := ordinary_sum_value_le φ _
    _ ≤ ∑ _j : J, B := Finset.sum_le_sum fun j _ ↦ (coeffValue_smul_le φ _ _).trans (hB j)
    _ = _ := by simp

/-- Grouped powers evaluate as powers at every point of the tensor spectrum. -/
theorem coeffValue_groupedPower (n : ℕ) (T : (∀ i, A i) → K) :
    coeffValue φ (groupedPower n T) = coeffValue φ T ^ n := by
  change normalizedSpectrum.toRingHom φ (ofRaw _) = normalizedSpectrum.toRingHom φ (ofRaw _) ^ n
  rw [ofRaw_groupedPower, map_pow]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
