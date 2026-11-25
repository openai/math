import OAI.LinearAlgebra.SpectralBooks.PatchPrice
import OAI.LinearAlgebra.SpectralBooks.Increment

/-! # Diagonal price inequalities on an embedded Euclidean patch

These properties are the inputs to the geometric part of the flat
diagonal law. Joint convexity and the metric bounds are only needed within
the embedded patch. Monotonicity and intersecting submodularity are properties
of the price on finite collections of sites.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open scoped Classical

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure DiagonalPriceLawsOn (C : Set E) (δ : Finset E → ℝ) : Prop where
  monotone : Monotone δ
  submodular : IntersectingSubmodular δ
  jointlyConvex : JointlyConvexPriceOn C δ
  wire : ∀ a ∈ C, ∀ b ∈ C, δ {a, b} = dist a b
  triangle_le : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, δ {a, b, c} ≤
    (dist a b + dist b c + dist c a) / 2

namespace DiagonalPriceLawsOn

variable {C : Set E} {δ : Finset E → ℝ} (H : DiagonalPriceLawsOn C δ)

include H

theorem mono_patch {C' : Set E} (h : C' ⊆ C) : DiagonalPriceLawsOn C' δ where
  monotone := H.monotone
  submodular := H.submodular
  jointlyConvex P hP hPC := H.jointlyConvex P hP fun p hp ↦ ⟨h (hPC p hp).1, h (hPC p hp).2⟩
  wire a ha b hb := H.wire a (h ha) b (h hb)
  triangle_le a ha b hb c hc := H.triangle_le a (h ha) b (h hb) c (h hc)

theorem singleton {a : E} (ha : a ∈ C) : δ {a} = 0 := by
  simpa using H.wire a ha a ha

theorem pair {a b : E} (ha : a ∈ C) (hb : b ∈ C) : δ {a,b} = dist a b := by
  exact H.wire a ha b hb

theorem nonneg (S : Finset E) (hS : S.Nonempty) (hSC : (S : Set E) ⊆ C) : 0 ≤ δ S := by
  obtain ⟨x, hx⟩ := hS
  exact (H.singleton (hSC hx)).symm.le.trans (H.monotone (Finset.singleton_subset_iff.mpr hx))

end DiagonalPriceLawsOn

end

end

end SpectralBooks
end LinearAlgebra
end OAI
