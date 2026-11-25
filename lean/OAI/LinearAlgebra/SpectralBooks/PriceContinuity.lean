import OAI.LinearAlgebra.SpectralBooks.Width
import OAI.LinearAlgebra.SpectralBooks.PlacementConvexity
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Uniform support bounds control polytope prices

A fixed polytope containing the unit ball absorbs errors in support values.
Separation of a point from a finite convex hull detects inclusion by testing
against unit vectors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open scoped RealInnerProductSpace Classical Pointwise
open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem mem_hull_of_forall_unit (T : Finset E) (hT : T.Nonempty) (x : E)
    (h : ∀ u : E, ‖u‖ = 1 → ∃ y ∈ convexHull ℝ (T : Set E), ⟪u, x⟫ ≤ ⟪u, y⟫) :
    x ∈ convexHull ℝ (T : Set E) := by
  by_contra hx
  obtain ⟨f, c, hf, hfx⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
    (T.finite_toSet.isClosed_convexHull ℝ) hx
  let w := (InnerProductSpace.toDual ℝ E).symm f
  have hw (y : E) : ⟪w, y⟫ = f y := InnerProductSpace.toDual_symm_apply
  have hpos : 0 < ‖w‖ := by
    by_contra! hn
    have hw0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
    have hz (y : E) : f y = 0 := by simpa [hw0] using (hw y).symm
    obtain ⟨t, ht⟩ := hT
    exact (lt_irrefl (0 : ℝ)) (by simpa [hz] using (hf t (subset_convexHull ℝ _ ht)).trans hfx)
  obtain ⟨y, hy, hxy⟩ := h (‖w‖⁻¹ • w) (by simp [norm_smul, hpos.ne'])
  simp only [real_inner_smul_left, hw] at hxy
  exact (not_le.mpr ((hf y hy).trans hfx)) (le_of_mul_le_mul_left hxy (inv_pos.mpr hpos))

private theorem subset_hull_add_of_support_le (S T Q : Finset E) (hS : S.Nonempty)
    (hT : T.Nonempty) (hQ : Q.Nonempty)
    (hball : closedBall (0 : E) 1 ⊆ convexHull ℝ (Q : Set E))
    (ε : ℝ)
    (h : ∀ u ∈ sphere (0 : E) 1, support S hS u ≤ support T hT u + ε) :
    (S : Set E) ⊆ convexHull ℝ ((T + Q.image (ε • ·) : Finset E) : Set E) := by
  intro x hx
  apply mem_hull_of_forall_unit _ (hT.add (hQ.image _))
  intro u hu
  have hus : u ∈ sphere (0 : E) 1 := by simpa using hu
  obtain ⟨y, hy, hsup⟩ := T.exists_mem_eq_sup' hT (fun y ↦ ⟪u, y⟫)
  refine ⟨y + ε • u, ?_, ?_⟩
  · rw [Finset.coe_add, Finset.coe_image, convexHull_add]
    have hscale : ε • u ∈ convexHull ℝ ((fun y : E ↦ ε • y) '' (Q : Set E)) := by
      change ε • u ∈ convexHull ℝ (ε • (Q : Set E))
      rw [convexHull_smul]
      exact Set.smul_mem_smul_set (hball (sphere_subset_closedBall hus))
    exact Set.add_mem_add (subset_convexHull ℝ (T : Set E) hy) hscale
  · have hl : ⟪u, x⟫ ≤ support S hS u := S.le_sup' _ hx
    have hr : support T hT u = ⟪u, y⟫ := hsup
    simpa only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu,
      one_pow, mul_one, hr] using hl.trans (h u hus)

/-- Uniform support approximation on the unit sphere bounds the price error by
the same error times the price of a fixed polytope containing the unit ball. -/
theorem exists_price_lipschitz_of_jointConvex (δ : Finset E → ℝ)
    (hjoint : JointlyConvexPrice δ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hscale : ∀ (S : Finset E), S.Nonempty → ∀ r : ℝ, 0 < r →
      δ (S.image (r • ·)) = r * δ S) :
    ∃ C : ℝ, ∀ ε > 0, ∀ S T : Finset E, ∀ hS : S.Nonempty, ∀ hT : T.Nonempty,
      (∀ u ∈ sphere (0 : E) 1, |support S hS u - support T hT u| ≤ ε) →
          |δ S - δ T| ≤ C * ε := by
  obtain ⟨Q, hQball, _⟩ := (convex_closedBall (0 : E) 1).exists_subset_interior_convexHull_finset_of_isCompact
    (isCompact_closedBall _ _) (t := Set.univ) Filter.univ_mem
  have hball := hQball.trans interior_subset
  have hQ : Q.Nonempty := by
    by_contra! h
    subst Q
    simpa using hball (show (0 : E) ∈ closedBall 0 1 by simp)
  refine ⟨δ Q, ?_⟩
  intro ε he S T hS hT h
  have hdir (A B : Finset E) (hA : A.Nonempty) (hB : B.Nonempty)
      (hAB : ∀ u ∈ sphere (0 : E) 1, support A hA u ≤ support B hB u + ε) :
      δ A ≤ δ B + ε * δ Q := by
    let P := B + Q.image (ε • ·)
    have hP : P.Nonempty := hB.add (hQ.image _)
    have hsub := subset_hull_add_of_support_le A B Q hA hB hQ hball ε hAB
    calc
      δ A ≤ δ (P ∪ A) := hmono hA Finset.subset_union_right
      _ = δ P := price_union_of_subset_convexHull δ hjoint hmono P A hP hsub
      _ ≤ δ B + δ (Q.image (ε • ·)) := price_add_le_of_jointConvex δ hjoint hscale
        B _ hB (hQ.image _)
      _ = _ := by rw [hscale Q hQ ε he]
  have hST := hdir S T hS hT (fun u hu ↦ by linarith [(abs_le.mp (h u hu)).2])
  have hTS := hdir T S hT hS (fun u hu ↦ by linarith [(abs_le.mp (h u hu)).1])
  rw [mul_comm]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI
