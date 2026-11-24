import OAI.Computability.VPVNP.ConfigurationCompletion
import OAI.Computability.VPVNP.FractionalGeodesic
import OAI.Computability.VPVNP.MetricMidpoints
import OAI.Computability.VPVNP.RealizedTransport
import OAI.Computability.VPVNP.SpectralMidpointTower
import OAI.Computability.VPVNP.WireCompletion
import OAI.Computability.VPVNP.WireCoupling

/-!
# The geodesic completion of a spectral wire pseudometric

Corollary 2.5 of *VP and VNP differ over every field* first forms the union
of successive midpoint extensions, then takes its metric completion.
The transport inequality guarantees that midpoints of Cauchy endpoint
sequences converge. Closure of finite configurations preserves spectral
realizability in the completion.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open WireTensor

/-- Fractional points in a space with spectral transport form a unique
constant-speed geodesic between any two endpoints. -/
theorem existsUnique_segment {X : Type*} [MetricSpace X] (hf : HasFractions X)
    (ht : FractionTransport X) (a b : X) :
    ∃! g : unitInterval → X, g 0 = a ∧ g 1 = b ∧
      ∀ s t, dist (g s) (g t) = |(s : ℝ) - t| * dist a b := by
  apply SpectralGeometry.existsUnique_constantSpeedSegment _ a b
  intro x y t
  obtain ⟨z, hz⟩ := hf x y t t.property.1 t.property.2
  exact ⟨z, hz, fun _ hw ↦ atFraction_unique ht t.property.1 t.property.2 hw hz⟩

/-- Any distance-preserving map of a pseudometric space into a metric space
induces an isometric embedding of the quotient identifying points at distance
zero. -/
theorem exists_separationQuotient_isometry {A X : Type*} [PseudoMetricSpace A] [MetricSpace X]
    (e : A → X) (he : ∀ a b, dist (e a) (e b) = dist a b) :
    ∃ f : SeparationQuotient A → X, Isometry f ∧ ∀ a, f (.mk a) = e a := by
  let f := SeparationQuotient.lift e (fun x y h ↦ dist_eq_zero.mp ((he x y).trans h.dist_eq_zero))
  refine ⟨f, Isometry.of_dist_eq ?_, fun _ ↦ rfl⟩
  intro x y
  obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk y
  exact he a b

/-- The completion step of Corollary 2.5, using six-point spectral transport
for Lemma 2.2. The isometric map sends exactly the pairs at wire distance
zero to the same point. -/
theorem exists_geodesic_completion_of_wire_transport {k : Type*} [Field k]
    {J : Type} [Fintype J] [Nontrivial J] (F : SpectralPoint k J)
    (hwire : ∀ (K : Type) [Fintype K] [Nontrivial K] (G : SpectralPoint k K),
      @FractionTransport K G.wirePseudoMetric) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : CompleteSpace X) (e : J → X),
      (∀ a b, dist (e a) (e b) = F.wireDistance a b) ∧
      RealizableConfigurations k X ∧ HasFractions X ∧ FractionTransport X ∧
      ∀ a b : X, ∃! g : unitInterval → X, g 0 = a ∧ g 1 = b ∧
        ∀ s t, dist (g s) (g t) = |(s : ℝ) - t| * dist a b := by
  obtain ⟨M, hJ, hR, hm⟩ := F.exists_midpoint_tower
  let : PseudoMetricSpace (J ⊕ ℕ) := M
  let X := UniformSpace.Completion (J ⊕ ℕ)
  have hX : RealizableConfigurations k X := fun n p ↦ RealizableUpToScale.completion (hR n) p
  have hT : FractionTransport X := fractionTransport_of_realizable hwire hX
  have hmid := midpoints_of_dense_isometry ((↑) : J ⊕ ℕ → X)
    UniformSpace.Completion.coe_isometry UniformSpace.Completion.denseRange_coe hm
    (fractionTransport_of_realizable hwire hR)
  have hf : HasFractions X := by
    intro x y t ht ht'
    apply SpectralGeometry.exists_fractionalPoint_of_midpoints _ x y ht ht'
    intro a b
    obtain ⟨z, hl, hr⟩ := hmid a b
    exact ⟨z, by linarith only [hl], by linarith only [hr]⟩
  exact ⟨X, inferInstance, inferInstance, fun a ↦ ((Sum.inl a : J ⊕ ℕ) : X),
    fun a b ↦ (UniformSpace.Completion.dist_eq _ _).trans (hJ a b),
    hX, hf, hT, existsUnique_segment hf hT⟩

/-- Corollary 2.5. Every finite spectral wire pseudometric embeds, after
identifying zero distances, into a complete geodesic space whose finite
configurations are realizable up to scale. Equation (2.2) holds throughout
the extension and the geodesic between each pair is unique. -/
theorem exists_geodesic_completion {k : Type*} [Field k]
    {J : Type} [Fintype J] [Nontrivial J] (F : SpectralPoint k J) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : CompleteSpace X) (e : J → X),
      (∀ a b, dist (e a) (e b) = F.wireDistance a b) ∧
      RealizableConfigurations k X ∧ HasFractions X ∧ FractionTransport X ∧
      ∀ a b : X, ∃! g : unitInterval → X, g 0 = a ∧ g 1 = b ∧
        ∀ s t, dist (g s) (g t) = |(s : ℝ) - t| * dist a b :=
  exists_geodesic_completion_of_wire_transport F (fun _ _ _ G ↦ G.fractionTransport)

end WireGeometry

end VPVNP
end Computability
end OAI
