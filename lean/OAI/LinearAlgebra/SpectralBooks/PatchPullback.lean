import OAI.LinearAlgebra.SpectralBooks.EuclideanPrice
import Mathlib.Analysis.Normed.Affine.Isometry

/-! # Restricting finite prices to an affine subspace -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open scoped Classical

/-- Intersecting submodularity pulls back along an injection of sites. -/
theorem IntersectingSubmodular.pullback {E F : Type*} [DecidableEq E] [DecidableEq F]
    {δ : Finset F → ℝ} (h : IntersectingSubmodular δ) (f : E → F) (hf : Function.Injective f) :
    IntersectingSubmodular (fun S ↦ δ (S.image f)) := by
  intro A B hI
  simpa only [Finset.image_union, Finset.image_inter A B hf] using
    h (A := A.image f) (B := B.image f) (Finset.image_inter A B hf ▸ hI.image f)

/-- Monotonicity of prices is preserved under a relabeling or an identification of sites. -/
theorem monotone_price_image {E F : Type*} [DecidableEq F] {δ : Finset F → ℝ}
    (h : Monotone δ) (f : E → F) : Monotone (fun S : Finset E ↦ δ (S.image f)) :=
  fun _ _ hST ↦ h (Finset.image_subset_image hST)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Joint convexity pulls back by any affine map carrying the source patch into
the target patch. In particular this applies to an affine isometry onto the
affine span of a finite configuration. -/
theorem JointlyConvexPriceOn.pullback {C : Set E} {C' : Set F} {δ : Finset F → ℝ}
    (hj : JointlyConvexPriceOn C' δ) (f : E →ᵃ[ℝ] F) (hf : Set.MapsTo f C C') :
    JointlyConvexPriceOn C (fun S ↦ δ (S.image f)) := by
  intro P hP hPC a b ha hb hab
  let pair := fun p : E × E ↦ (f p.1, f p.2)
  have hmap : ∀ p ∈ P.image pair, p.1 ∈ C' ∧ p.2 ∈ C' := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hf (hPC q hq).1, hf (hPC q hq).2⟩
  have h := hj (P.image pair) (hP.image _) hmap a b ha hb hab
  have hcomb (p : E × E) : f (a • p.1 + b • p.2) = a • f p.1 + b • f p.2 := by
    rw [show a = 1-b by linarith, ← AffineMap.lineMap_apply_module, ← AffineMap.lineMap_apply_module]
    exact f.apply_lineMap _ _ _
  simpa only [pair, Finset.image_image, Function.comp_def, hcomb] using h

/-- Restrict all the diagonal price laws along an affine isometric embedding. -/
theorem DiagonalPriceLawsOn.comp_affineIsometry {C : Set F} {δ : Finset F → ℝ}
    (H : DiagonalPriceLawsOn C δ) (f : E →ᵃⁱ[ℝ] F) :
    DiagonalPriceLawsOn (f ⁻¹' C) (fun S ↦ δ (S.image f)) where
  monotone := monotone_price_image H.monotone f
  submodular := H.submodular.pullback f f.injective
  jointlyConvex := H.jointlyConvex.pullback f.toAffineMap (fun _ hx ↦ hx)
  wire a ha b hb := by simpa using H.wire (f a) ha (f b) hb
  triangle_le := by
    intro a ha b hb c hc
    simpa using H.triangle_le (f a) ha (f b) hb (f c) hc

end

end

end SpectralBooks
end LinearAlgebra
end OAI
