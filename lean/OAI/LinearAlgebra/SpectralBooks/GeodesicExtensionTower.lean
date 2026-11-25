import OAI.LinearAlgebra.SpectralBooks.SpectralSpace

/-! # Iterating finite midpoint extensions of spectral spaces

Starting from one-point extensions preserving all old prices, insert
midpoints for every pair of sites in a finite configuration. Iterating
these finite enlargements gives a countable system of spectral spaces.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open SiteTensor

variable {K : Type*} [Field K]

/-- An isometry that preserves the price of every finite placement. -/
structure PriceEmbedding {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (P : SpectralPlacementPrices K X) (Q : SpectralPlacementPrices K Y) where
  map : X → Y
  isometry : Isometry map
  price {I : Type} [Fintype I] (T : Raw.{0} I K) (p : I → X) :
    Q.price T (map ∘ p) = P.price T p

namespace PriceEmbedding

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
  {P : SpectralPlacementPrices K X} {Q : SpectralPlacementPrices K Y}
  {R : SpectralPlacementPrices K Z}

/-- Identity price embedding. -/
def refl (P : SpectralPlacementPrices K X) : PriceEmbedding P P :=
  ⟨id, isometry_id, fun _ _ ↦ rfl⟩

/-- Successive price-preserving embeddings. -/
def trans (f : PriceEmbedding P Q) (g : PriceEmbedding Q R) : PriceEmbedding P R :=
  ⟨g.map ∘ f.map, g.isometry.comp f.isometry, fun T p ↦
    (g.price T (f.map ∘ p)).trans (f.price T p)⟩

end PriceEmbedding

/-- The two distances prescribing an exact midpoint. -/
def IsWireMidpoint {X : Type*} [PseudoMetricSpace X] (a b m : X) : Prop :=
  dist a m = dist a b / 2 ∧ dist b m = dist a b / 2

theorem IsWireMidpoint.map {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {a b m : X} (h : IsWireMidpoint a b m) {f : X → Y} (hf : Isometry f) :
    IsWireMidpoint (f a) (f b) (f m) := by
  simpa only [IsWireMidpoint, hf.dist_eq] using h

/-- Finite metric realizations of spectral prices over the fixed field. -/
structure FinitePriceSpace (K : Type*) [Field K] where
  carrier : Type
  metric : MetricSpace carrier
  finite : Finite carrier
  prices : @SpectralPlacementPrices K _ carrier metric.toPseudoMetricSpace

attribute [instance] FinitePriceSpace.metric FinitePriceSpace.finite

/-- Finite one-new-party interpolation in a metric realization. -/
def HasFiniteMidpointExtensions (K : Type*) [Field K] : Prop :=
  ∀ (A : FinitePriceSpace K) (a b : A.carrier), ∃ (B : FinitePriceSpace K)
    (f : PriceEmbedding A.prices B.prices) (m : B.carrier), IsWireMidpoint (f.map a) (f.map b) m

private theorem insert_finite_midpoints (h : HasFiniteMidpointExtensions K) (A : FinitePriceSpace K)
    (s : Finset (A.carrier × A.carrier)) :
    ∃ (B : FinitePriceSpace K) (f : PriceEmbedding A.prices B.prices),
      ∀ p ∈ s, ∃ m, IsWireMidpoint (f.map p.1) (f.map p.2) m := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨A, PriceEmbedding.refl _, by simp⟩
  | @insert p s _ ih =>
    obtain ⟨B, f, hs⟩ := ih
    obtain ⟨C, g, m, hm⟩ := h B (f.map p.1) (f.map p.2)
    refine ⟨C, f.trans g, fun q hq ↦ ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ⟨m, hm⟩
    obtain ⟨n, hn⟩ := hs q hq
    exact ⟨g.map n, hn.map g.isometry⟩

/-- One finite enlargement inserts midpoints for every pair of old sites. -/
theorem HasFiniteMidpointExtensions.all_pairs (h : HasFiniteMidpointExtensions K)
    (A : FinitePriceSpace K) :
    ∃ (B : FinitePriceSpace K) (f : PriceEmbedding A.prices B.prices),
      ∀ a b, ∃ m, IsWireMidpoint (f.map a) (f.map b) m := by
  classical
  let := Fintype.ofFinite A.carrier
  obtain ⟨B, f, hf⟩ := insert_finite_midpoints h A Finset.univ
  exact ⟨B, f, fun a b ↦ hf (a,b) (Finset.mem_univ _)⟩

/-- A sequence in which the next finite spectral space realizes all midpoints
of the previous one. -/
structure MidpointTower (K : Type*) [Field K] where
  stage : ℕ → FinitePriceSpace K
  step n : PriceEmbedding (stage n).prices (stage (n + 1)).prices
  midpoint n (a b : (stage n).carrier) :
    ∃ m, IsWireMidpoint ((step n).map a) ((step n).map b) m

/-- Any finite spectral space starts a midpoint tower. -/
theorem HasFiniteMidpointExtensions.tower (h : HasFiniteMidpointExtensions K)
    (A : FinitePriceSpace K) :
    ∃ T : MidpointTower K, Nonempty (PriceEmbedding A.prices (T.stage 0).prices) := by
  classical
  choose next embed mid using h.all_pairs
  let stage : ℕ → FinitePriceSpace K := Nat.rec A (fun _ B ↦ next B)
  let T : MidpointTower K := ⟨stage, fun n ↦ embed (stage n), fun n ↦ mid (stage n)⟩
  exact ⟨T, ⟨PriceEmbedding.refl _⟩⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI
