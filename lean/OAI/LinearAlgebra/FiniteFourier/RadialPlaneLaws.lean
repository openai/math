import OAI.LinearAlgebra.FiniteFourier.CharacterSaturation
import OAI.LinearAlgebra.FiniteFourier.TangentPlane
import OAI.LinearAlgebra.SpectralBooks.GridCubeExtension

/-! # Geometric laws of the homogeneous spectral plane

The spectral flat diagonal theorem determines the common-label price.
The common-label copying degeneration gives the copying inequality. The
single radial blowup therefore satisfies all three geometric laws required
in the character-table saturation argument.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open HyperbolicObstruction Set
open scoped Classical

variable {K : Type*} [Field K]

/-- A sublinear price obeys the synchronized geodesic convexity inequality
on Euclidean placements. -/
theorem spectralPlane_jointlyConvexDiagonal (P : SpectralPlacementPrices K Plane)
    (hsub : ∀ {I : Type} [Fintype I] [Nonempty I], SublinearPrice (P.price (Raw.diagonal I K (Fin 2)))) :
    P.JointlyConvexDiagonal (innerProductSpace_catZero Plane) := by
  let hE := innerProductSpace_catZero Plane
  intro I _ _ x y t ht
  have hseg (i : I) : CATZero.segment hE (x i) (y i) t = (1-t) • x i + t • y i := by
    rw [← AffineMap.lineMap_apply_module]
    symm
    apply CATZero.eq_segment_of_dist hE ht
    · rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht.1]
    · rw [dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
  change P.price (Raw.diagonal I K (Fin 2)) (fun i ↦ CATZero.segment hE (x i) (y i) t) ≤ _
  simp only [hseg]
  have h := hsub (I := I)
  exact (h.add_le ((1-t) • x) (t • y)).trans_eq
    (congrArg₂ (· + ·) (h.hom _ (sub_nonneg.mpr ht.2) _) (h.hom _ ht.1 _))

/-- Sublinearity of the actual placed binary diagonals implies their flat law
in the plane. -/
theorem fourier_flat_law_of_sublinear (P : SpectralPlacementPrices K Plane)
    (hsub : ∀ {I : Type} [Fintype I] [Nonempty I], SublinearPrice (P.price (Raw.diagonal I K (Fin 2))))
    (S : Finset Plane) (hS : S.Nonempty) : P.diagonal S = meanWidth S hS := by
  simpa using P.flatDiagonalLaw_isometry (innerProductSpace_catZero Plane)
    (spectralPlane_jointlyConvexDiagonal P hsub) isometry_id S hS

/-- Sublinearity suffices for all the additional laws of the spectral plane:
flat diagonal prices and copying follow for the actual assignment. -/
theorem fourierPlaneLaws_of_sublinear (P : SpectralPlacementPrices K Plane)
    (hsub : ∀ {I : Type} [Fintype I] (T : Raw.{0} I K), SublinearPrice (P.price T)) :
    FourierPlaneLaws P :=
  ⟨hsub, fourier_flat_law_of_sublinear P (fun {_} _ _ ↦ hsub _)⟩

/-- Starting with a jointly convex spectral plane over `K`, the canonical
radial blowup gives a single assignment satisfying all Fourier plane laws. -/
theorem tangentPlane_fourierPlaneLaws (P : SpectralPlacementPrices K Plane)
    (hc : ∀ {I : Type} [Fintype I] (T : Raw.{0} I K), ConvexOn ℝ univ (P.price T)) :
    FourierPlaneLaws (tangentPlane P) :=
  fourierPlaneLaws_of_sublinear _ (fun T ↦ tangentPlane_sublinear P T (hc T))

end

end

end FiniteFourier
end LinearAlgebra
end OAI
