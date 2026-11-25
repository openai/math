import OAI.LinearAlgebra.SpectralBooks.NonTreePlane
import OAI.LinearAlgebra.SpectralBooks.Theorem
import OAI.LinearAlgebra.SpectralBooks.GeodesicExtension
import OAI.LinearAlgebra.SpectralBooks.ConvexOnPrice

/-!
# The plane side of the spectral tree-or-plane alternative

The four-point defect is measured at an actual normalized point of the
finite-party tensor spectrum. Its complete geodesic realization is CAT(0).
The geometric non-tree implication produces a Euclidean spectral plane, and
the price of every fixed tensor is convex in the tuple of all its positions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open SiteTensor

/-- A characteristic is on the plane side when some finite tensor spectrum in
that characteristic violates the four-point condition of a tree metric. -/
def HasNonTreeWireMetric (K : Type*) [Field K] : Prop :=
  ∃ (J : Type) (_ : Fintype J) (_ : Nonempty J)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (a b z w : J),
    let d := rawWireDistance φ 1
    max (d a z + d b w) (d a w + d b z) < d a b + d z w

/-- A single finite non-tree wire metric gives a jointly convex spectral
price system on the whole Euclidean plane, over its original field. -/
theorem exists_jointly_convex_spectral_plane {K : Type*} [Field K]
    (h : HasNonTreeWireMetric K) :
    ∃ P : SpectralPlacementPrices K (EuclideanSpace ℝ (Fin 2)),
      ∀ {I : Type} [Fintype I] (T : Raw.{0} I K), ConvexOn ℝ Set.univ (P.price T) := by
  obtain ⟨J, _, _, φ, a, b, z, w, hbad⟩ := h
  obtain ⟨Y, _, P, p, _, hg, hdist, _⟩ :=
    SpectralPlacementPrices.realize_finite_point_geodesic φ 1 zero_le_one
  obtain ⟨Q⟩ := spectralPlane_of_fourPointDefect P (P.catZero hg) (p a) (p b) (p z) (p w)
    (by simpa only [hdist] using hbad)
  exact ⟨Q, fun T ↦ Q.convexOn_price T⟩

end SpectralBooks
end LinearAlgebra
end OAI
