import OAI.Computability.BorderVNP.CoverFrameProducts

/-!
# Pulling finite configuration bins back through tile charts

Ties on seams are assigned exact representatives. The representatives may jump
there. Almost-everywhere continuity is sufficient for the finite-product Hecke
motion estimate on configuration bins, since the seams and the bin boundaries
have zero mass for the ideal law.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CoverFrameMixing

open MeasureTheory Set Finset Filter
open scoped Topology

/-- A point of continuity outside the preimage of the target frontier is
outside the frontier of the preimage. -/
theorem notMem_preimage_frontier {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {B : Set Y} {x : X} (hc : ContinuousAt f x) (hb : f x ∉ frontier B) :
    x ∉ frontier (f ⁻¹' B) := by
  have h : f x ∈ interior B ∪ interior Bᶜ := by
    rwa [← compl_frontier_eq_union_interior]
  rcases h with h | h
  · have hpre : f ⁻¹' B ∈ 𝓝 x := hc (mem_interior_iff_mem_nhds.mp h)
    exact disjoint_interior_frontier.notMem_of_mem_left (mem_interior_iff_mem_nhds.mpr hpre)
  · have hpre : (f ⁻¹' B)ᶜ ∈ 𝓝 x := hc (mem_interior_iff_mem_nhds.mp h)
    simpa [frontier_compl] using disjoint_interior_frontier.notMem_of_mem_left
      (mem_interior_iff_mem_nhds.mpr hpre)

/-- A bin of null frontier still has null frontier when pulled back through a
measure-preserving chart that is continuous off the seams. -/
theorem chart_frontier_null {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} (hp : MeasurePreserving f μ ν)
    (hc : ∀ᵐ x ∂μ, ContinuousAt f x) {B : Set Y} (hb : ν (frontier B) = 0) :
    μ (frontier (f ⁻¹' B)) = 0 := by
  have hn : μ (f ⁻¹' frontier B) = 0 :=
    (hp.measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet).trans hb
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hc, measure_eq_zero_iff_ae_notMem.mp hn] with x h h'
  exact notMem_preimage_frontier h h'

end CoverFrameMixing

namespace Hecke

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

variable {G I : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Fintype I]
    (Γ : Subgroup G) (z : G) [Fintype (Cosets (intersection Γ z))]
    [MeasurableSpace (Cosets Γ)] [OpensMeasurableSpace (Cosets Γ)] [CompactSpace (Cosets Γ)]
    [SecondCountableTopology (Cosets Γ)] [TopologicalSpace.PseudoMetrizableSpace (Cosets Γ)]
    (μ : Measure (Cosets Γ)) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

/-- The true finite word distribution approximates configuration-bin probabilities
uniformly in the product starting frame, with a different chart allowed for each
of the finitely many relative segment types. -/
theorem product_chart_bin_estimate {Y J T : Type*} [Finite J] [Finite T] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (hμ : ∀ f : Cosets Γ →ᵇ ℝ, (∫ y, operator Γ z f y ∂μ) = ∫ y, f y ∂μ)
    (hd : Dense (Subgroup.closure ((Γ : Set G) ∪ {z}) : Set G))
    (chart : T → (I → Cosets Γ) → Y) (ν : T → Measure Y)
    (hp : ∀ t, MeasurePreserving (chart t) (Measure.pi (fun _ : I => μ)) (ν t))
    (hc : ∀ t, ∀ᵐ y ∂Measure.pi (fun _ : I => μ), ContinuousAt (chart t) y)
    (bin : T → J → Set Y) (hB : ∀ t j, MeasurableSet (bin t j))
    (hnull : ∀ t j, ν t (frontier (bin t j)) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t j (x : I → G),
      |(productLaw Γ z n x).toMeasure.real (chart t ⁻¹' bin t j) - (ν t).real (bin t j)| < ε := by
  rw [Filter.eventually_all]
  intro t
  have h := product_bin_estimate Γ z μ hμ hd (fun j => chart t ⁻¹' bin t j)
    (fun j => CoverFrameMixing.chart_frontier_null (hp t) (hc t) (hnull t j)) hε
  filter_upwards [h] with n hn j x
  have he := congrArg ENNReal.toReal ((hp t).measure_preimage (hB t j).nullMeasurableSet)
  change (Measure.pi (fun _ : I => μ)).real (chart t ⁻¹' bin t j) = (ν t).real (bin t j) at he
  rw [← he]
  exact hn j x

end Hecke

end BorderVNP
end Computability
end OAI
