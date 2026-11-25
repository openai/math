import OAI.LinearAlgebra.SpectralBooks.PriceBlowup
import OAI.LinearAlgebra.SpectralBooks.FinitePriceSpace
import OAI.LinearAlgebra.SpectralBooks.FiniteMetricModel

/-! # Finite spectral realizations on an open patch of a normed space -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set Topology

universe w
variable {K V : Type*} [Field K] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Each nonempty finite subset of a patch has the distances, up to positive scale,
of a configuration in a spectral space over the fixed field. Values of the placement
away from the finite subset are unrestricted. -/
def HasFiniteSpectralRealizationsOn (K : Type*) [Field K] {Y : Type*} [MetricSpace Y]
    (U : Set Y) : Prop :=
  ∀ S : Finset Y, S.Nonempty → (S : Set Y) ⊆ U →
    ∃ (X : Type w) (_ : MetricSpace X) (_ : SpectralPlacementPrices K X) (c : ℝ),
      0 < c ∧ ∃ f : Y → X, ∀ p ∈ S, ∀ q ∈ S, dist (f p) (f q) = c * dist p q

/-- A translation followed by uniform shrinking puts any finite configuration in the patch. -/
theorem exists_scaled_configuration_in_open {U : Set V} (hU : U.Nonempty) (ho : IsOpen U)
    (S : Finset V) : ∃ a : V, ∃ s : ℝ, 0 < s ∧ ∀ p ∈ S, a + s • p ∈ U := by
  obtain ⟨a, ha⟩ := hU
  have he : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ p ∈ S, a + s • p ∈ U := by
    apply (Filter.eventually_all_finset S).mpr
    intro p _
    have ht : Tendsto (fun s : ℝ ↦ a + s • p) (𝓝[>] 0) (𝓝 a) := by
      simpa using ((tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).smul_const p).const_add a
    exact ht (ho.mem_nhds ha)
  obtain ⟨s, hs, hpos⟩ := (he.and self_mem_nhdsWithin).exists
  exact ⟨a, s, hpos, hs⟩

/-- To realize an arbitrary finite configuration, first move it into the open patch
and multiply the two positive scales. -/
theorem HasFiniteSpectralRealizationsOn.univ_of_open {U : Set V}
    (h : HasFiniteSpectralRealizationsOn.{w} K U) (hne : U.Nonempty) (ho : IsOpen U) :
    HasFiniteSpectralRealizationsOn.{w} K (Set.univ : Set V) := by
  classical
  intro S hS _
  obtain ⟨a, s, hs, hpatch⟩ := exists_scaled_configuration_in_open hne ho S
  let j (p : V) := a + s • p
  have hsub : (↑(S.image j) : Set V) ⊆ U := by
    rintro _ hp
    obtain ⟨p, hmem, rfl⟩ := Finset.mem_image.mp hp
    exact hpatch p hmem
  obtain ⟨X, m, P, c, hc, f, hf⟩ := h (S.image j) (hS.image j) hsub
  refine ⟨X, m, P, c * s, mul_pos hc hs, f ∘ j, ?_⟩
  intro p hp q hq
  rw [Function.comp_apply, Function.comp_apply,
    hf _ (Finset.mem_image_of_mem j hp) _ (Finset.mem_image_of_mem j hq)]
  simp [j, dist_smul₀, Real.norm_of_nonneg hs.le, mul_assoc]

/-- An isometric embedding of the patch into one spectral space realizes every finite
configuration in the patch. -/
theorem HasFiniteSpectralRealizationsOn.of_isometry {X : Type w} [MetricSpace X]
    {Y : Type*} [MetricSpace Y]
    (P : SpectralPlacementPrices K X) {U : Set Y} (f : U → X) (hf : Isometry f) :
    HasFiniteSpectralRealizationsOn.{w} K U := by
  classical
  intro S hS hSU
  obtain ⟨p, hp⟩ := hS
  let j (v : Y) : U := if hv : v ∈ U then ⟨v, hv⟩ else ⟨p, hSU hp⟩
  refine ⟨X, inferInstance, P, 1, zero_lt_one, f ∘ j, ?_⟩
  intro x hx y hy
  simp [hf.dist_eq, j, hSU hx, hSU hy, Subtype.dist_eq]

/-- An ultrafilter on finite subsets makes all the finite realizations compatible.
Each fixed pair of distances agrees exactly after rescaling on a tail. -/
theorem HasFiniteSpectralRealizationsOn.prices {Y : Type*} [MetricSpace Y] [Nonempty Y]
    (h : HasFiniteSpectralRealizationsOn.{w} K (Set.univ : Set Y)) :
    Nonempty (SpectralPlacementPrices K Y) := by
  classical
  let o : Y := Classical.arbitrary Y
  choose X m P c hc f hf using fun S : Finset Y ↦
    h (insert o S) (Finset.insert_nonempty _ _) (Set.subset_univ _)
  let ω := Ultrafilter.of (atTop : Filter (Finset Y))
  refine ⟨SpectralPlacementPrices.blowupFamily P ω c hc f o fun x y ↦ ?_⟩
  apply Tendsto.mono_left _ (Ultrafilter.of_le _)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ({x,y} : Finset Y)] with S hS
  rw [hf _ _ (Finset.mem_insert_of_mem (hS (by simp))) _
    (Finset.mem_insert_of_mem (hS (by simp))), mul_div_cancel_left₀ _ (hc S).ne']

/-- The distances of a finite normalized spectral wire metric give a spectral-space
realization on taking the metric quotient of its sites. -/
theorem hasFiniteSpectralRealizationsOn_of_wireMetrics {Y : Type*} [MetricSpace Y] {U : Set Y}
    (h : ∀ S : Finset Y, S.Nonempty → (S : Set Y) ⊆ U →
      ∃ (J : Type) (_ : Fintype J) (_ : Nonempty J)
        (φ : normalizedSpectrum ((· ≤ ·) : SiteTensor.TensorClass.{0} J K → _ → Prop))
        (c : ℝ), 0 < c ∧ ∃ f : Y → J, ∀ p ∈ S, ∀ q ∈ S,
          SiteTensor.rawWireDistance φ 1 (f p) (f q) = c * dist p q) :
    HasFiniteSpectralRealizationsOn.{0} K U := by
  intro S hs hsub
  obtain ⟨J, _, _, φ, c, hc, f, hf⟩ := h S hs hsub
  obtain ⟨X, m, P, ι, _, hdist, _⟩ :=
    SiteTensor.exists_metric_price_realization φ 1 zero_le_one
  exact ⟨X, m, P, c, hc, ι ∘ f, fun p hp q hq ↦ (hdist _ _).trans (hf p hp q hq)⟩

/-- A finite metric model in a spectral space inherits global spectral prices over the
same field. The individual placements in the model may be unrelated. -/
theorem spectralPrices_of_finite_scaled_models {X : Type w} [PseudoMetricSpace X]
    {Y : Type*} [MetricSpace Y] [Nonempty Y] (h : ScaledFiniteMetricModel X Y)
    (P : SpectralPlacementPrices K X) : Nonempty (SpectralPlacementPrices K Y) := by
  classical
  apply HasFiniteSpectralRealizationsOn.prices.{w}
  intro S hS _
  obtain ⟨o, ho⟩ := hS
  let e : (↑S : Set Y) ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  obtain ⟨c, hc, q, hq⟩ := h (fun i ↦ (e.symm i).val)
  let j (x : Y) : (↑S : Set Y) := if hx : x ∈ S then ⟨x, hx⟩ else ⟨o, ho⟩
  refine ⟨SeparationQuotient X, inferInstance, P.separationQuotient, c, hc,
    fun x ↦ SeparationQuotient.mk (q (e (j x))), ?_⟩
  intro x hx y hy
  simp [SeparationQuotient.dist_mk, hq, j, hx, hy]

/-- Isometric finite metric models give the scale-one case. -/
theorem FiniteMetricModel.spectralPrices {X : Type w} [PseudoMetricSpace X]
    {Y : Type*} [MetricSpace Y] [Nonempty Y] (h : FiniteMetricModel X Y)
    (P : SpectralPlacementPrices K X) : Nonempty (SpectralPlacementPrices K Y) := by
  apply spectralPrices_of_finite_scaled_models _ P
  intro I _ p
  obtain ⟨q, hq⟩ := h p
  exact ⟨1, zero_lt_one, q, by simpa using hq⟩

end SpectralBooks
end LinearAlgebra
end OAI
