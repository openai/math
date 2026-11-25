import OAI.Geometry.HyperbolicGroups.CATZero
import OAI.LinearAlgebra.SpectralBooks.DiagonalMonotonicity
import OAI.LinearAlgebra.SpectralBooks.FlatLaw
import OAI.LinearAlgebra.SpectralBooks.IntersectingSubmodularity
import OAI.LinearAlgebra.SpectralBooks.TriangleSemiperimeter

/-! # The flat diagonal law for spectral placement prices

Synchronized geodesic convexity is the geometric input. Monotonicity,
intersecting submodularity, and the triangle semiperimeter upper bound follow
from the evaluations of the concrete tensors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open HyperbolicObstruction Set
open scoped Classical

section

theorem IntersectingSubmodular.image_of_monotone {A B : Type*} {δ : Finset B → ℝ}
    (h : IntersectingSubmodular δ) (hmono : Monotone δ) (f : A → B) :
    IntersectingSubmodular (fun S : Finset A ↦ δ (S.image f)) := by
  intro S T hST
  have hsub := Finset.image_inter_subset f S T
  have hi := h (A := S.image f) (B := T.image f) ((hST.image f).mono hsub)
  dsimp only
  rw [Finset.image_union]
  exact (add_le_add_right (hmono hsub) _).trans hi

namespace SpectralPlacementPrices

open SiteTensor

variable {K : Type*} {X : Type} [Field K] [MetricSpace X] (P : SpectralPlacementPrices K X)
  (hX : CATZero X)

/-- Joint price convexity for the binary common diagonal along geodesics.
This is the specialization of the cited joint convexity theorem to a placed
diagonal tensor. -/
def JointlyConvexDiagonal : Prop :=
  ∀ {I : Type} [Fintype I] [Nonempty I] (p q : I → X) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
    P.price (Raw.diagonal I K (Fin 2)) (fun i ↦ CATZero.segment hX (p i) (q i) t) ≤
      (1-t) * P.price (Raw.diagonal I K (Fin 2)) p + t * P.price (Raw.diagonal I K (Fin 2)) q

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Euclidean convex combinations in the patch follow the unique geodesics.
The price of their binary diagonal is therefore jointly convex. -/
theorem jointlyConvexPriceOn_chart (hjoint : P.JointlyConvexDiagonal hX) {C : Set E}
    (hc : Convex ℝ C) {e : E → X} (he : ∀ x ∈ C, ∀ y ∈ C, dist (e x) (e y) = dist x y) :
    JointlyConvexPriceOn C (fun S ↦ P.diagonal (S.image e)) := by
  intro T hT hTC a b ha hb hab
  let : Nonempty T := hT.to_subtype
  have ht : b ∈ Icc (0 : ℝ) 1 := ⟨hb, by linarith⟩
  have hba : 1-b = a := by linarith
  have hcomb (p : T) : CATZero.segment hX (e p.val.1) (e p.val.2) b = e (a • p.val.1 + b • p.val.2) := by
    obtain ⟨hx,hy⟩ := hTC _ p.property
    rw [← hba, ← AffineMap.lineMap_apply_module]
    have hz := hc.lineMap_mem hx hy ht
    symm
    apply CATZero.eq_segment_of_dist hX ht
    · rw [he _ hx _ hz, he _ hx _ hy, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg hb]
    · rw [he _ hz _ hy, he _ hx _ hy, dist_comm (AffineMap.lineMap _ _ _), dist_right_lineMap,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
  have h := hjoint (I := T) (fun p ↦ e p.val.1) (fun p ↦ e p.val.2) b ht
  simp only [hcomb, P.price_binaryDiagonal_eq, hba] at h
  have him (f : E × E → E) :
      Finset.univ.image (fun p : T ↦ e (f p.val)) = (T.image f).image e := by
    ext x
    simp
  simpa only [him (fun p ↦ a • p.1 + b • p.2), him Prod.fst, him Prod.snd] using h

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Flat diagonal law on a convex Euclidean patch, from the spectral geometry
inputs for that patch and intersecting submodularity of the ambient diagonal. -/
theorem flatDiagonalLaw_chart_of_submodular
    (hsub : IntersectingSubmodular P.diagonal) (hjoint : P.JointlyConvexDiagonal hX)
    {C : Set E} (hc : Convex ℝ C) {e : E → X}
    (he : ∀ x ∈ C, ∀ y ∈ C, dist (e x) (e y) = dist x y)
    (htriangle : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C,
      P.diagonal {e a, e b, e c} = (dist a b + dist b c + dist c a) / 2)
    (S : Finset E) (hS : S.Nonempty) (hSC : (S : Set E) ⊆ C) :
    P.diagonal (S.image e) = meanWidth S hS := by
  apply flatDiagonalLaw (C := C) (δ := fun T ↦ P.diagonal (T.image e)) _ hc S hS hSC
  exact ⟨fun _ _ h ↦ P.diagonal_mono (Finset.image_subset_image h),
    hsub.image_of_monotone P.diagonal_mono e, P.jointlyConvexPriceOn_chart hX hjoint hc he,
    fun a ha b hb ↦ by simpa [he a ha b hb] using P.diagonal_pair (e a) (e b),
    fun a ha b hb c hc ↦ by simpa using (htriangle a ha b hb c hc).le⟩

/-- The flat diagonal law for a genuine spectral price over any field, given
synchronized geodesic convexity of its placed binary diagonal. -/
theorem flatDiagonalLaw_chart (hjoint : P.JointlyConvexDiagonal hX)
    {C : Set E} (hc : Convex ℝ C) {e : E → X}
    (he : ∀ x ∈ C, ∀ y ∈ C, dist (e x) (e y) = dist x y)
    (S : Finset E) (hS : S.Nonempty) (hSC : (S : Set E) ⊆ C) :
    P.diagonal (S.image e) = meanWidth S hS := by
  apply flatDiagonalLaw (C := C) (δ := fun T ↦ P.diagonal (T.image e)) _ hc S hS hSC
  exact ⟨fun _ _ h ↦ P.diagonal_mono (Finset.image_subset_image h),
    P.intersectingSubmodular.image_of_monotone P.diagonal_mono e,
    P.jointlyConvexPriceOn_chart hX hjoint hc he,
    fun a ha b hb ↦ by simpa [he a ha b hb] using P.diagonal_pair (e a) (e b),
    fun a ha b hb c hc ↦ by
      simpa [he a ha b hb, he b hb c hc, he c hc a ha] using
        P.diagonal_triangle_le_half_perimeter (e a) (e b) (e c)⟩

/-- The specialization to a complete Euclidean flat in a spectral space. -/
theorem flatDiagonalLaw_isometry (hjoint : P.JointlyConvexDiagonal hX)
    {e : E → X} (he : Isometry e) (S : Finset E) (hS : S.Nonempty) :
    P.diagonal (S.image e) = meanWidth S hS :=
  P.flatDiagonalLaw_chart hX hjoint convex_univ (fun x _ y _ ↦ he.dist_eq x y)
    S hS (subset_univ _)

end SpectralPlacementPrices

end

end

end SpectralBooks
end LinearAlgebra
end OAI
