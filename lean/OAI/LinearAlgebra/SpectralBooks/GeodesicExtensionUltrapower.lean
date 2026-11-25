import OAI.LinearAlgebra.SpectralBooks.GeodesicExtensionTower
import OAI.LinearAlgebra.SpectralBooks.GeodesicExtensionSegments
import OAI.LinearAlgebra.SpectralBooks.MetricLimitComplete
import OAI.LinearAlgebra.SpectralBooks.SpectralMetricLimit

/-! # A complete geodesic extension of a spectral space with exact midpoints

Constant sequences preserve every finite placement price in the metric ultrapower.
Choosing midpoints coordinatewise gives exact midpoints in that complete space.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
section

open Filter Topology HyperbolicObstruction MetricLimit

universe u
variable {X : Type u} [MetricSpace X]

private theorem metricLimit_has_midpoints (U : Ultrafilter ℕ) (o : X)
    (hm : ∀ a b : X, ∃ m, IsWireMidpoint a b m) :
    ∀ a b : Space (U := U) (X := fun _ ↦ X) (o := fun _ ↦ o), ∃ m, IsWireMidpoint a b m := by
  intro a b
  obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk a
  obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk b
  choose v hv using fun n ↦ hm (a.val n) (b.val n)
  obtain ⟨R, hR⟩ := a.bound
  obtain ⟨D, hD⟩ := bounded_dist a b
  let m : Bounded U (fun _ ↦ X) (fun _ ↦ o) := ⟨v, R + D / 2, fun n ↦ by
    have ht := dist_triangle o (a.val n) (v n)
    rw [(hv n).1] at ht
    linarith [hR n, (hD n).2]⟩
  refine ⟨point m, ?_, ?_⟩
  · apply tendsto_nhds_unique (tendsto_point_dist a m)
    apply ((tendsto_point_dist a b).div_const 2).congr'
    exact Eventually.of_forall fun n ↦ (hv n).1.symm
  · apply tendsto_nhds_unique (tendsto_point_dist b m)
    apply ((tendsto_point_dist a b).div_const 2).congr'
    exact Eventually.of_forall fun n ↦ (hv n).2.symm

/-- A complete geodesic spectral space containing a price-preserving isometric copy
of a pointed spectral space with exact midpoints. -/
theorem exists_complete_geodesic_price_extension {K : Type*} [Field K]
    (P : SpectralPlacementPrices K X) (o : X) (hmid : ∀ a b : X, ∃ m, IsWireMidpoint a b m) :
    ∃ (Y : Type u) (_ : MetricSpace Y) (Q : SpectralPlacementPrices K Y),
      Nonempty (PriceEmbedding P Q) ∧ CompleteSpace Y ∧ IsGeodesic Y := by
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let Y := Space (U := U) (X := fun _ ↦ X) (o := fun _ ↦ o)
  let c (x : X) : Bounded U (fun _ ↦ X) (fun _ ↦ o) := ⟨fun _ ↦ x, dist o x, fun _ ↦ le_rfl⟩
  let Q : SpectralPlacementPrices K Y := SpectralPlacementPrices.metricLimit U (fun _ ↦ P)
  let f : PriceEmbedding P Q := {
    map := point ∘ c
    isometry := Isometry.of_dist_eq fun x y ↦ tendsto_nhds_unique
      (tendsto_point_dist (c x) (c y)) tendsto_const_nhds
    price := fun T p ↦ tendsto_nhds_unique
      (SpectralPlacementPrices.metricLimit_price_tendsto U (fun _ ↦ P) T (c ∘ p)) tendsto_const_nhds }
  let : CompleteSpace Y := completeSpace_metricLimit (Ultrafilter.of_le atTop)
  choose mid h using metricLimit_has_midpoints U o hmid
  refine ⟨Y, inferInstance, Q, ⟨f⟩, inferInstance, isGeodesic_of_exactMidpoints mid ?_⟩
  exact fun a b ↦ ⟨(h a b).1, (dist_comm _ _).trans (h a b).2⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI
