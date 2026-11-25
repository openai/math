import Mathlib.Analysis.Convex.Intrinsic

/-! # Centering a Euclidean patch in its affine span -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A nonempty convex patch admits affine Euclidean coordinates centered at a
relative interior point. This also applies to a singleton in its zero-dimensional span. -/
theorem exists_centered_affinePatch {C : Set E} (hC : Convex ℝ C) (hne : C.Nonempty) :
    ∃ i : (affineSpan ℝ C).direction →ᵃⁱ[ℝ] E,
      C ⊆ range i ∧ (0 : (affineSpan ℝ C).direction) ∈ interior (i ⁻¹' C) := by
  let A := affineSpan ℝ C
  obtain ⟨x, hx⟩ := hne
  let : Nonempty A := ⟨⟨x, subset_affineSpan ℝ C hx⟩⟩
  obtain ⟨_, ⟨z, hz, rfl⟩⟩ := Set.Nonempty.intrinsicInterior hC (show C.Nonempty from ⟨x, hx⟩)
  let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ z
  let i := A.subtypeₐᵢ.comp e.toAffineIsometry
  refine ⟨i, ?_, ?_⟩
  · intro y hy
    let y' : A := ⟨y, subset_affineSpan ℝ C hy⟩
    obtain ⟨v, hv⟩ := e.surjective y'
    exact ⟨v, congrArg Subtype.val hv⟩
  · let B : Set A := Subtype.val ⁻¹' C
    change 0 ∈ interior (e.toHomeomorph ⁻¹' B)
    rw [← e.toHomeomorph.preimage_interior]
    change e 0 ∈ interior B
    simpa [e] using hz

end SpectralBooks
end LinearAlgebra
end OAI
