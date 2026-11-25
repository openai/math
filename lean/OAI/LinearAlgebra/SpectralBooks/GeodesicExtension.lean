import OAI.LinearAlgebra.SpectralBooks.MidpointTower.GeodesicExtensionUnion
import OAI.LinearAlgebra.SpectralBooks.GeodesicExtensionUltrapower
import OAI.LinearAlgebra.SpectralBooks.FiniteIntervalExtension

/-! # Complete geodesic extensions of finite spectral configurations

Finite one-party interpolation suffices to realize every finite spectral price
in a complete geodesic space over the same ground field. The embedding
preserves the prices of all tensors, including placements with repeated sites.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

section

open HyperbolicObstruction SiteTensor

variable {K : Type*} [Field K]

/-- Pass from finite one-point interpolation to a complete geodesic spectral
space preserving every old placement price. -/
theorem HasFiniteMidpointExtensions.complete_geodesic_extension
    (h : HasFiniteMidpointExtensions K) (A : FinitePriceSpace K) (o : A.carrier) :
    ∃ (Y : Type) (_ : MetricSpace Y) (Q : SpectralPlacementPrices K Y),
      Nonempty (PriceEmbedding A.prices Q) ∧ CompleteSpace Y ∧ IsGeodesic Y := by
  obtain ⟨T, ⟨f⟩⟩ := h.tower A
  obtain ⟨X, _, P, ⟨g⟩, hm⟩ := T.exists_midpoint_union (f.map o)
  obtain ⟨Y, met, Q, ⟨j⟩, complete, geodesic⟩ :=
    exists_complete_geodesic_price_extension P (g.map (f.map o)) hm
  exact ⟨Y, met, Q, ⟨(f.trans g).trans j⟩, complete, geodesic⟩

/-- A single complete geodesic space realizes all the finite placed values
at the prescribed scaled normalized spectral point. -/
theorem HasFiniteMidpointExtensions.realize_point (h : HasFiniteMidpointExtensions K)
    {J : Type} [Fintype J] [Nonempty J]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c) :
    ∃ (Y : Type) (_ : MetricSpace Y) (Q : SpectralPlacementPrices K Y) (p : J → Y),
      CompleteSpace Y ∧ IsGeodesic Y ∧
      (∀ a b, dist (p a) (p b) = rawWireDistance φ c a b) ∧
      ∀ {I : Type} [Fintype I] (T : Raw.{0} I K) (v : I → J),
        Q.price T (p ∘ v) = rawLogPrice φ c (T.group v) := by
  obtain ⟨X, met, P, q, hq, hd, hp⟩ := exists_metric_price_realization φ c hc
  let A : FinitePriceSpace K := ⟨X, met, Finite.of_surjective q hq, P⟩
  obtain ⟨Y, metY, Q, ⟨f⟩, hy, hgeo⟩ := h.complete_geodesic_extension A (q (Classical.arbitrary J))
  exact ⟨Y, metY, Q, f.map ∘ q, hy, hgeo, fun a b ↦ (f.isometry.dist_eq _ _).trans (hd a b),
    fun T v ↦ (f.price T (q ∘ v)).trans (hp T v)⟩

/-- Every nonempty finite spectral space over any field embeds in a complete
geodesic spectral space over that field, with all original prices preserved. -/
theorem FinitePriceSpace.exists_complete_geodesic_extension (A : FinitePriceSpace K)
    (o : A.carrier) :
    ∃ (Y : Type) (_ : MetricSpace Y) (Q : SpectralPlacementPrices K Y),
      Nonempty (PriceEmbedding A.prices Q) ∧ CompleteSpace Y ∧ IsGeodesic Y :=
  SpectralPlacementPrices.exists_finite_midpoint_extension.complete_geodesic_extension A o

/-- Every finite normalized point, at any nonnegative scale, has a complete
geodesic metric realization. The same placement computes all raw tensor
prices and all wire distances. -/
theorem SpectralPlacementPrices.realize_finite_point_geodesic
    {J : Type} [Fintype J] [Nonempty J]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c) :
    ∃ (Y : Type) (_ : MetricSpace Y) (Q : SpectralPlacementPrices K Y) (p : J → Y),
      CompleteSpace Y ∧ IsGeodesic Y ∧
      (∀ a b, dist (p a) (p b) = rawWireDistance φ c a b) ∧
      ∀ {I : Type} [Fintype I] (T : Raw.{0} I K) (v : I → J),
        Q.price T (p ∘ v) = rawLogPrice φ c (T.group v) :=
  exists_finite_midpoint_extension.realize_point φ c hc

end

end

end SpectralBooks
end LinearAlgebra
end OAI
