import OAI.Computability.VPVNP.SpectralSectorDistance
import OAI.Computability.VPVNP.SpectralOppositeRays
import OAI.Computability.VPVNP.TangentRatio
import OAI.Computability.VPVNP.SpectralMidpointToCAT
import OAI.Computability.VPVNP.RealizedTransport

/-!
# The squared midpoint inequality for wire metric spaces

Section 4.1 rescales the three segments from a midpoint to the three
marked vertices. In each tangent sector the distance from the first ray at
time `t` to the second ray at time one obeys a Euclidean quadratic law.
The triangle inequality between the opposite rays at arbitrary `t` forces
the comparison at the original midpoint. Saturation forces each original
sector to have its Euclidean distances at every parameter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open Set

variable (k : Type*) [Field k] {X : Type*} [MetricSpace X] {o x y z : X}

private theorem tangentRay_vertex_sq (hf : HasFractions X) (hT : FractionTransport X)
    (hTT : FractionTransport (Tangent o)) (hr : RealizableConfigurations k X)
    (a : RadialSegment o x) (c : RadialSegment o z) (t : ℝ) (ht : 0 ≤ t) :
    dist (tangentRay a t) (tangentRay c 1) ^ 2 =
      t ^ 2 * dist o x ^ 2 + dist o z ^ 2 +
        t * (radialSlope a c ^ 2 - dist o x ^ 2 - dist o z ^ 2) := by
  let f := tangent_hasFractions hf o
  let A := tangentRay a
  let C := tangentRay c
  have hc (r : ℝ) (hr : r ∈ Ici 0) : dist (A r) (C r) = radialSlope a c * r :=
    tangentRay_cross hT a c hr
  have haxis₁ := sectorPoint_axis_left f A C hc ht (show t ∈ Ici 0 from ht)
  have haxis₂ := sectorPoint_axis_right f A C hc (r := 1) zero_le_one (by norm_num : (1 : ℝ) ∈ Ici 0)
  let p : ℝ × ℝ := (t, 0)
  let q : ℝ × ℝ := (0, 1)
  have hp : p ∈ sectorDomain (Ici 0) := ⟨ht, le_rfl, by simpa [p] using ht⟩
  have hq : q ∈ sectorDomain (Ici 0) := ⟨le_rfl, zero_le_one, by norm_num [q]⟩
  have hsq := sectorPoint_dist_sq k f hTT (tangent_realizableConfigurations hr o)
    (convex_Ici _) (by norm_num : (0 : ℝ) ∈ Ici 0) (by norm_num : (1 : ℝ) ∈ Ici 0)
    (fun _ hr _ hs ↦ tangentRay_speed a hr hs) (fun _ hr _ hs ↦ tangentRay_speed c hr hs)
    hc hp hq
  have heq : dist (A t) (C 1) = dist (sectorPoint f A C p) (sectorPoint f A C q) := calc
    dist (A t) (C 1) = dist (C 1) (A t) := dist_comm _ _
    _ = dist (C 1) (sectorPoint f A C p) := PseudoMetricSpace.dist_eq_of_dist_zero _ haxis₁
    _ = dist (sectorPoint f A C p) (C 1) := dist_comm _ _
    _ = _ := (PseudoMetricSpace.dist_eq_of_dist_zero _ haxis₂).symm
  change dist (A t) (C 1) ^ 2 = _
  rw [heq, hsq]
  dsimp only [p,q]
  ring

private theorem opposite_slopes (hf : HasFractions X) (hT : FractionTransport X)
    (hTT : FractionTransport (Tangent o)) (hr : RealizableConfigurations k X)
    (ho : AtFraction x y (1 / 2) o) (a : RadialSegment o x) (b : RadialSegment o y)
    (c : RadialSegment o z) :
    2 * (dist o x ^ 2 + dist o z ^ 2) ≤ radialSlope a c ^ 2 + radialSlope b c ^ 2 := by
  have hx := ho.1
  rw [dist_comm x o] at hx
  have hy : dist o y = dist o x := by linarith only [hx, ho.2]
  apply opposite_ray_quadratic_bound dist_nonneg
    (fun t ↦ dist (tangentRay a t) (tangentRay c 1)) (fun t ↦ dist (tangentRay b t) (tangentRay c 1))
  · intro t ht
    rw [← tangentRay_opposite hT ho a b ht, dist_comm (tangentRay b t) (tangentRay c 1)]
    exact dist_triangle _ _ _
  · exact tangentRay_vertex_sq k hf hT hTT hr a c
  · intro t ht
    simpa only [hy] using tangentRay_vertex_sq k hf hT hTT hr b c t ht

/-- Lemma 4.1's inequality when the segment transport inequalities (2.2)
are given in the space and its rescaling at the marked midpoint. -/
theorem squared_midpoint_of_transport (hf : HasFractions X) (hT : FractionTransport X)
    (hTT : FractionTransport (Tangent o)) (hr : RealizableConfigurations k X)
    (ho : AtFraction x y (1 / 2) o) (z : X) :
    2 * dist z o ^ 2 + (1 / 2 : ℝ) * dist x y ^ 2 ≤ dist z x ^ 2 + dist z y ^ 2 := by
  obtain ⟨a⟩ := exists_radialSegment hf hT o x
  obtain ⟨b⟩ := exists_radialSegment hf hT o y
  obtain ⟨c⟩ := exists_radialSegment hf hT o z
  have h := opposite_slopes k hf hT hTT hr ho a b c
  have h₁ := (sq_le_sq₀ (radialSlope_nonneg a c) dist_nonneg).mpr (radialSlope_le_dist a c)
  have h₂ := (sq_le_sq₀ (radialSlope_nonneg b c) dist_nonneg).mpr (radialSlope_le_dist b c)
  have hx := ho.1
  rw [dist_comm x o] at hx
  rw [dist_comm z x, dist_comm z y, dist_comm z o]
  rw [hx] at h
  linarith only [h, h₁, h₂]

/-- Euclidean (possibly degenerate) distances throughout the filled sector
of two segments. The mixed coefficient is determined by the three boundary
lengths, as in the Euclidean cosine rule. -/
def IsEuclideanSector (hf : HasFractions X) (a : RadialSegment o x) (c : RadialSegment o z) : Prop :=
  ∀ p ∈ sectorDomain (Icc (0 : ℝ) 1), ∀ q ∈ sectorDomain (Icc (0 : ℝ) 1),
    dist (sectorPoint hf a.path c.path p) (sectorPoint hf a.path c.path q) ^ 2 =
      (p.1 - q.1) ^ 2 * dist o x ^ 2 + (p.2 - q.2) ^ 2 * dist o z ^ 2 +
      (p.1 - q.1) * (p.2 - q.2) * (dist o x ^ 2 + dist o z ^ 2 - dist x z ^ 2)

private theorem euclideanSector_of_endpointSlope (hf : HasFractions X) (hT : FractionTransport X)
    (hr : RealizableConfigurations k X) (a : RadialSegment o x) (c : RadialSegment o z)
    (h : radialSlope a c = dist x z) : IsEuclideanSector hf a c := by
  have hc := (radialSlope_eq_endpoint hT a c).mp h
  rw [h] at hc
  intro p hp q hq
  exact sectorPoint_dist_sq k hf hT hr (convex_Icc _ _) (by simp) (by simp)
    a.speed c.speed hc hp hq

/-- At equality in Lemma 4.1, both sectors based at the midpoint, joining
the third vertex to each endpoint, are Euclidean throughout. -/
theorem euclideanSectors_of_midpoint_eq (hf : HasFractions X) (hT : FractionTransport X)
    (hTT : FractionTransport (Tangent o)) (hr : RealizableConfigurations k X)
    (ho : AtFraction x y (1 / 2) o) (a : RadialSegment o x) (b : RadialSegment o y)
    (c : RadialSegment o z) (heq : 2 * dist z o ^ 2 + (1 / 2 : ℝ) * dist x y ^ 2 =
      dist z x ^ 2 + dist z y ^ 2) : IsEuclideanSector hf a c ∧ IsEuclideanSector hf b c := by
  have h := opposite_slopes k hf hT hTT hr ho a b c
  have h₁ := (sq_le_sq₀ (radialSlope_nonneg a c) dist_nonneg).mpr (radialSlope_le_dist a c)
  have h₂ := (sq_le_sq₀ (radialSlope_nonneg b c) dist_nonneg).mpr (radialSlope_le_dist b c)
  have hx := ho.1
  rw [dist_comm x o] at hx
  rw [dist_comm z x, dist_comm z y, dist_comm z o] at heq
  rw [hx] at h
  constructor
  · apply euclideanSector_of_endpointSlope k hf hT hr
    apply (sq_eq_sq₀ (radialSlope_nonneg a c) dist_nonneg).mp
    linarith only [h, h₁, h₂, heq]
  · apply euclideanSector_of_endpointSlope k hf hT hr
    apply (sq_eq_sq₀ (radialSlope_nonneg b c) dist_nonneg).mp
    linarith only [h, h₁, h₂, heq]

/-- Equation (4.2) from spectral configurations, using the six-point wire
transport law of Lemma 2.2. No completeness assumption on the target is needed. -/
theorem hasCATZeroSegments_of_wire_transport
    (hwire : ∀ (J : Type) [Fintype J] [Nontrivial J] (F : WireTensor.SpectralPoint k J),
      @FractionTransport J F.wirePseudoMetric)
    (hf : HasFractions X) (hr : RealizableConfigurations k X) :
    SpectralGeometry.HasCATZeroSegments X := by
  have hT : FractionTransport X := fractionTransport_of_realizable hwire hr
  apply hasCATZeroSegments_of_midpoint hf hT
  intro x y z o ho
  exact squared_midpoint_of_transport k hf hT
    (fractionTransport_of_realizable hwire (tangent_realizableConfigurations hr o)) hr ho z

/-- The equality assertion of Lemma 4.1 under the same six-point wire
transport law. The formula applies to every marked point in both sectors. -/
theorem euclideanSectors_of_wire_transport
    (hwire : ∀ (J : Type) [Fintype J] [Nontrivial J] (F : WireTensor.SpectralPoint k J),
      @FractionTransport J F.wirePseudoMetric)
    (hf : HasFractions X) (hr : RealizableConfigurations k X)
    (ho : AtFraction x y (1 / 2) o) (a : RadialSegment o x) (b : RadialSegment o y)
    (c : RadialSegment o z) (heq : 2 * dist z o ^ 2 + (1 / 2 : ℝ) * dist x y ^ 2 =
      dist z x ^ 2 + dist z y ^ 2) : IsEuclideanSector hf a c ∧ IsEuclideanSector hf b c :=
  euclideanSectors_of_midpoint_eq k hf (fractionTransport_of_realizable hwire hr)
    (fractionTransport_of_realizable hwire (tangent_realizableConfigurations hr o)) hr ho a b c heq

end WireGeometry

end VPVNP
end Computability
end OAI
