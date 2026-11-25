import OAI.LinearAlgebra.SpectralBooks.GeodesicExtension
import OAI.LinearAlgebra.SpectralBooks.SpectralUltralimit.GeodesicExtensionFilter

/-!
# Complete geodesic extension of an arbitrary pointed spectral space

Realize every finite subset together with the base point in a geodesic
spectral space. The ultrafilter on finite subsets contains every inclusion
tail. Consequently each fixed finite list of sites retains all distances
and tensor prices in the metric ultralimit.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

section

open Filter Topology HyperbolicObstruction SiteTensor

universe u
variable {X : Type u} [MetricSpace X] {K : Type*} [Field K]

/-- Outside the finite set, assign the base point. This gives a uniformly
bounded section for each old point in the eventual ultralimit. -/
private theorem finite_midpoint_model (P : SpectralPlacementPrices K X) (o : X) (S : Finset X) :
    ∃ (Y : Type) (_ : MetricSpace Y) (Q : SpectralPlacementPrices K Y) (g : X → Y),
      (∀ a b : Y, ∃ m, IsWireMidpoint a b m) ∧
      (∀ x, dist (g o) (g x) ≤ dist o x) ∧
      (∀ x ∈ S, ∀ y ∈ S, dist (g x) (g y) = dist x y) ∧
      ∀ {I : Type} [Fintype I] (T : Raw.{0} I K) (p : I → X), (∀ i, p i ∈ S) →
        Q.price T (g ∘ p) = P.price T p := by
  classical
  let F := insert o S
  let e := Fintype.equivFin (↥F)
  let E : Fin (Fintype.card (↥F)) ↪ X := e.symm.toEmbedding.trans (Function.Embedding.subtype _)
  let := MetricSpace.induced E E.injective inferInstance
  have hE : Isometry E := Isometry.of_dist_eq fun _ _ ↦ rfl
  let r (x : X) : Fin (Fintype.card (↥F)) :=
    e (if hx : x ∈ F then ⟨x, hx⟩ else ⟨o, Finset.mem_insert_self ..⟩)
  have hre (x : X) (hx : x ∈ F) : E (r x) = x := by simp [E, e, r, hx]
  have ho : o ∈ F := Finset.mem_insert_self ..
  let A : FinitePriceSpace K := ⟨_, inferInstance, inferInstance, P.pullback E hE⟩
  obtain ⟨T, ⟨f⟩⟩ := SpectralPlacementPrices.exists_finite_midpoint_extension.tower A
  obtain ⟨Y, met, Q, ⟨j⟩, hmid⟩ := T.exists_midpoint_union (f.map (r o))
  let g := f.trans j
  have hd (x y : X) (hx : x ∈ F) (hy : y ∈ F) :
      dist (g.map (r x)) (g.map (r y)) = dist x y := by
    rw [g.isometry.dist_eq]
    change dist (E (r x)) (E (r y)) = _
    rw [hre x hx, hre y hy]
  refine ⟨Y, met, Q, g.map ∘ r, hmid, fun x ↦ ?_, fun x hx y hy ↦ ?_, ?_⟩
  · by_cases hx : x ∈ F
    · exact (hd o x ho hx).le
    · have hrx : r x = r o := by simp [r, hx, ho]
      simpa only [Function.comp_apply, hrx, dist_self] using (dist_nonneg : 0 ≤ dist o x)
  · exact hd x y (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy)
  · intro I _ T p hp
    have h := g.price T (r ∘ p)
    change Q.price T (g.map ∘ (r ∘ p)) = P.price T (E ∘ (r ∘ p)) at h
    have heq : E ∘ (r ∘ p) = p := funext fun i ↦ hre (p i) (Finset.mem_insert_of_mem (hp i))
    exact h.trans (congrArg (P.price T) heq)

/-- Every pointed spectral space admits a price-preserving isometric embedding
in a complete geodesic spectral space over the same field. -/
theorem SpectralPlacementPrices.exists_complete_geodesic_extension
    (P : SpectralPlacementPrices K X) (o : X) :
    ∃ (Y : Type u) (_ : MetricSpace Y) (Q : SpectralPlacementPrices K Y),
      Nonempty (PriceEmbedding P Q) ∧ CompleteSpace Y ∧ IsGeodesic Y := by
  classical
  choose Z met H g hmid hb hd hp using finite_midpoint_model P o
  let U := Ultrafilter.of (atTop : Filter (Finset X))
  let base (S : Finset X) := g S o
  let sec (x : X) : SpectralUltralimit.Section Z base :=
    ⟨fun S ↦ g S x, dist o x, fun S ↦ hb S x⟩
  let Q := SpectralUltralimit.prices U H base
  let f : PriceEmbedding P Q := {
    map := SpectralUltralimit.point U ∘ sec
    isometry := by
      apply Isometry.of_dist_eq
      intro x y
      apply tendsto_nhds_unique (SpectralUltralimit.tendsto_dist U (sec x) (sec y))
      apply tendsto_const_nhds.congr'
      filter_upwards [Ultrafilter.of_le atTop (eventually_ge_atTop ({x, y} : Finset X))] with S hS
      exact (hd S x (hS (by simp)) y (hS (by simp))).symm
    price := by
      intro I _ T p
      apply tendsto_nhds_unique (SpectralUltralimit.tendsto_price U H T (sec ∘ p))
      apply tendsto_const_nhds.congr'
      filter_upwards [Ultrafilter.of_le atTop (eventually_ge_atTop (Finset.univ.image p))] with S hS
      exact (hp S T p (fun i ↦ hS (Finset.mem_image_of_mem p (Finset.mem_univ i)))).symm }
  obtain ⟨Y, metY, QY, ⟨j⟩, hY, hg⟩ := exists_complete_geodesic_price_extension Q (f.map o)
    (SpectralUltralimit.exists_midpoints U base hmid)
  exact ⟨Y, metY, QY, ⟨f.trans j⟩, hY, hg⟩

/-- Every spectral space embeds in a complete geodesic spectral space. The
empty space already has both properties. -/
theorem SpectralPlacementPrices.exists_complete_geodesic_extension_unpointed
    (P : SpectralPlacementPrices K X) :
    ∃ (Y : Type u) (_ : MetricSpace Y) (Q : SpectralPlacementPrices K Y),
      Nonempty (PriceEmbedding P Q) ∧ CompleteSpace Y ∧ IsGeodesic Y := by
  cases isEmpty_or_nonempty X with
  | inl h => exact ⟨X, inferInstance, P, ⟨PriceEmbedding.refl P⟩, inferInstance, fun a ↦ isEmptyElim a⟩
  | inr h => exact P.exists_complete_geodesic_extension h.some

end

end

end SpectralBooks
end LinearAlgebra
end OAI
