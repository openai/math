import OAI.LinearAlgebra.SpectralBooks.FinitePlaneCriterion
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TreeWirePacket

/-! # The four-point condition for finite wire prices

A violation at a normalized point persists in its geodesic spectral
realization. Curvature then produces a spectral Euclidean plane.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor

variable {K : Type*} [Field K] {I : Type} [Fintype I] [Nonempty I]

/-- On the tree side, the sum on the two crossing pairs is at most the
larger of the sums on the two side matchings. -/
theorem rawWireDistance_fourPoint_of_tree (tree : ¬ HasNonTreeWireMetric K)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)) (a b c d : I) :
    rawWireDistance φ 1 a c + rawWireDistance φ 1 b d ≤
      max (rawWireDistance φ 1 a b + rawWireDistance φ 1 c d)
          (rawWireDistance φ 1 a d + rawWireDistance φ 1 b c) := by
  apply le_of_not_gt
  intro h
  apply tree
  refine ⟨I, inferInstance, inferInstance, φ, a, c, b, d, ?_⟩
  simpa only [rawWireDistance_symm φ 1 c b] using h

/-- Over a field admitting no spectral Euclidean plane, the binary wire
distances of each finite normalized point satisfy the tree four-point inequality. -/
theorem rawWireDistance_fourPoint_of_no_plane
    (noPlane : ¬ Nonempty (SpectralPlacementPrices K (EuclideanSpace ℝ (Fin 2))))
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)) (a b c d : I) :
    rawWireDistance φ 1 a c + rawWireDistance φ 1 b d ≤
      max (rawWireDistance φ 1 a b + rawWireDistance φ 1 c d)
          (rawWireDistance φ 1 a d + rawWireDistance φ 1 b c) := by
  exact rawWireDistance_fourPoint_of_tree
    (fun h ↦ noPlane ⟨(exists_jointly_convex_spectral_plane h).choose⟩) φ a b c d

/-- Absence of a spectral plane gives ordinary tree straightening of a packet
of parallel crossing bits, at every positive tolerance. -/
theorem exists_wire_packet_of_no_plane
    (noPlane : ¬ Nonempty (SpectralPlacementPrices K (EuclideanSpace ℝ (Fin 2))))
    (a b c d : I) {σ : ℝ} (hσ : 0 < σ) : HasWirePacket K a b c d σ :=
  exists_tree_wire_packet K a b c d
    (fun φ ↦ rawWireDistance_fourPoint_of_no_plane noPlane φ a b c d) hσ

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
