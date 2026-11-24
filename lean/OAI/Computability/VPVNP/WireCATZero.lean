import OAI.Computability.VPVNP.GeodesicExtension
import OAI.Computability.VPVNP.SpectralCurvature
import OAI.Computability.VPVNP.SpectralGeometry
import OAI.Computability.VPVNP.WireCoupling

/-!
# CAT(0) completion and the six-party wire inequality

Combining Corollary 2.5, the shifted crossing rigidity, and the squared
midpoint comparison yields a complete CAT(0) target for each spectral point.
The completion still has finite configurations realized by spectral points
over the same coefficient field. Lemma 6.2 then applies to its six wire parties.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open WireTensor SpectralGeometry

/-- Every geodesic space with finite configurations realized by wire metrics
satisfies the CAT(0) squared-distance comparison (4.2). -/
theorem hasCATZeroSegments_of_realizable (k : Type*) [Field k] {X : Type*} [MetricSpace X]
    (hf : HasFractions X) (hr : RealizableConfigurations k X) : HasCATZeroSegments X :=
  hasCATZeroSegments_of_wire_transport k (fun _ _ _ G ↦ G.fractionTransport) hf hr

/-- At equality in Lemma 4.1, the sectors based at the midpoint and ending
at the third vertex are Euclidean throughout. -/
theorem euclideanSectors_of_realizable (k : Type*) [Field k] {X : Type*} [MetricSpace X]
    (hf : HasFractions X) (hr : RealizableConfigurations k X) {o x y z : X}
    (ho : AtFraction x y (1 / 2) o) (a : RadialSegment o x) (b : RadialSegment o y)
    (c : RadialSegment o z) (heq : 2 * dist z o ^ 2 + (1 / 2 : ℝ) * dist x y ^ 2 =
      dist z x ^ 2 + dist z y ^ 2) : IsEuclideanSector hf a c ∧ IsEuclideanSector hf b c :=
  euclideanSectors_of_wire_transport k (fun _ _ _ G ↦ G.fractionTransport) hf hr ho a b c heq

end WireGeometry

namespace WireTensor.SpectralPoint

open WireGeometry SpectralGeometry

variable {k : Type*} [Field k] {J : Type} [Fintype J] [Nontrivial J] (F : SpectralPoint k J)

/-- A complete CAT(0) space realizes all the distances of the given wire
pseudometric. Its own finite distance arrays remain spectrally realizable. -/
theorem exists_catZero_completion :
    ∃ (X : Type) (_ : MetricSpace X) (_ : CompleteSpace X) (e : J → X),
      (∀ a b, dist (e a) (e b) = F.wireDistance a b) ∧
      RealizableConfigurations k X ∧ HasCATZeroSegments X := by
  obtain ⟨X, _, _, e, he, hr, hf, _, _⟩ :=
    exists_geodesic_completion_of_wire_transport F (fun _ _ _ G ↦ G.fractionTransport)
  exact ⟨X, inferInstance, inferInstance, e, he, hr, hasCATZeroSegments_of_realizable k hf hr⟩

/-- Distance-preserving CAT(0) realization used in the cube obstruction. -/
theorem catZero_embedding :
    ∃ (X : Type) (_ : MetricSpace X) (_ : HasCATZeroSegments X) (e : J → X),
      ∀ a b, dist (e a) (e b) = F.wireDistance a b := by
  obtain ⟨X, _, _, e, he, _, hc⟩ := F.exists_catZero_completion
  exact ⟨X, inferInstance, hc, e, he⟩

/-- Lemma 6.2 for the actual six-party wire distances of a spectral point. -/
theorem sixParty_wire_energy (a b c d m n : J) :
    (1 / 3 : ℝ) * F.wireDistance a b ^ 2 + F.wireDistance c d ^ 2 ≤
      (31 / 16 : ℝ) * ((8 / 31 : ℝ) * (F.wireDistance a c ^ 2 + F.wireDistance b c ^ 2) +
        (4 / 31 : ℝ) * (F.wireDistance a m ^ 2 + F.wireDistance b n ^ 2) +
        (40 / 93 : ℝ) * (F.wireDistance c m ^ 2 + F.wireDistance c n ^ 2) +
        (16 / 31 : ℝ) * (F.wireDistance d m ^ 2 + F.wireDistance d n ^ 2)) := by
  obtain ⟨X, _, hc, e, he⟩ := F.catZero_embedding
  simpa only [he] using sixParty_energy hc (e a) (e b) (e c) (e d) (e m) (e n)

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI
