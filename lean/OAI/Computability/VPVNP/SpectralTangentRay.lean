import OAI.Computability.VPVNP.SpectralTangent
import OAI.Computability.VPVNP.FractionalGeodesic
import Mathlib.Tactic.FieldSimp

/-!
# Rays in the rescaled tangent space

The rescaling of three geodesic segments in Lemma 4.1 produces rays. For
each pair with common origin their equal-parameter distance is exactly
linear, with slope the infimum of the original positive-parameter ratios.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open Filter Set Topology

variable {X : Type*} [MetricSpace X]

/-- A constant-speed geodesic on the unit interval, represented by a total
function on the real line for the coordinate sector constructions. -/
structure RadialSegment (o x : X) where
  /-- Parametrized path that runs at constant speed from the basepoint at zero to its endpoint
  at one. -/
  path : ℝ → X
  start : path 0 = o
  finish : path 1 = x
  speed : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
    dist (path r) (path s) = dist o x * |r-s|

theorem exists_radialSegment (hf : HasFractions X) (hT : FractionTransport X) (o x : X) :
    Nonempty (RadialSegment o x) := by
  obtain ⟨g, hg0, hg1, hg⟩ := SpectralGeometry.exists_constantSpeedSegment
    (fun a b t ↦ by
      obtain ⟨z, hz⟩ := hf a b t t.property.1 t.property.2
      exact ⟨z, hz, fun w hw ↦ atFraction_unique hT t.property.1 t.property.2 hw hz⟩) o x
  let p (t : ℝ) := if h : t ∈ Icc (0 : ℝ) 1 then g ⟨t,h⟩ else o
  refine ⟨⟨p, ?_, ?_, ?_⟩⟩
  · simpa [p] using hg0
  · simpa [p] using hg1
  · intro r hr s hs
    simpa only [p, dite_eq_left hr, dite_eq_left hs, mul_comm] using hg ⟨r,hr⟩ ⟨s,hs⟩

variable {o x y : X}

private theorem RadialSegment.origin_dist (a : RadialSegment o x) (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
    dist o (a.path r) = r * dist o x := by
  simpa only [zero_sub, abs_neg, abs_of_nonneg hr.1, a.start, mul_comm] using a.speed 0 (by simp) r hr

private theorem RadialSegment.fraction (a : RadialSegment o x) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : 0 < t) (ht' : t ≤ 1) : AtFraction o (a.path t) (s/t) (a.path s) := by
  have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs, hst.trans ht'⟩
  have htI : t ∈ Icc (0:ℝ) 1 := ⟨ht.le, ht'⟩
  constructor
  · rw [a.origin_dist _ hs', a.origin_dist _ htI]
    field_simp
  · rw [a.speed s hs' t htI, a.origin_dist _ htI, abs_of_nonpos (sub_nonpos.mpr hst)]
    field_simp
    ring

theorem radial_ratio_mono (hT : FractionTransport X) (a : RadialSegment o x) (b : RadialSegment o y) :
    MonotoneOn (fun t ↦ dist (a.path t) (b.path t) / t) (Ioc 0 1) := by
  intro s hs t ht hst
  have h := hT (div_nonneg hs.1.le ht.1.le) ((div_le_one ht.1).mpr hst)
    (a.fraction hs.1.le hst ht.1 ht.2) (b.fraction hs.1.le hst ht.1 ht.2)
  rw [dist_self, mul_zero, zero_add] at h
  apply (div_le_iff₀ hs.1).mpr
  convert h using 1
  ring

/-- The speed of separation in the tangent cone. -/
noncomputable def radialSlope (a : RadialSegment o x) (b : RadialSegment o y) : ℝ :=
  sInf ((fun t ↦ dist (a.path t) (b.path t)/t) '' Ioc 0 1)

theorem radialSlope_le_ratio (a : RadialSegment o x) (b : RadialSegment o y) {t : ℝ} (ht : t ∈ Ioc 0 1) :
    radialSlope a b ≤ dist (a.path t) (b.path t)/t := by
  apply csInf_le _ (mem_image_of_mem _ ht)
  exact ⟨0, fun _ ⟨s, hs, h⟩ ↦ h ▸ div_nonneg dist_nonneg hs.1.le⟩

theorem radialSlope_le_dist (a : RadialSegment o x) (b : RadialSegment o y) :
    radialSlope a b ≤ dist x y := by
  simpa only [a.finish, b.finish, div_one] using
    radialSlope_le_ratio a b (t := 1) ⟨zero_lt_one, le_rfl⟩

private noncomputable def rayValue (a : RadialSegment o x) (r : ℝ) (n : ℕ) : X :=
  if r / tangentScale n ∈ Icc 0 1 then a.path (r / tangentScale n) else o

/-- Rescaling a segment produces a ray defined at every nonnegative time. -/
noncomputable def tangentRay (a : RadialSegment o x) (r : ℝ) : Tangent o := by
  refine ⟨rayValue a r, max 0 r * dist o x, fun n ↦ ?_⟩
  unfold rayValue
  split_ifs with ht
  · rw [a.origin_dist _ ht, ← mul_assoc, mul_div_cancel₀ r (tangentScale_pos n).ne']
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
  · simp only [dist_self, mul_zero]
    exact mul_nonneg (le_max_left _ _) dist_nonneg

private theorem parameter_eventually (r : ℝ) (hr : 0 ≤ r) :
    ∀ᶠ n : ℕ in atTop, r / tangentScale n ∈ Icc 0 1 := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop r] with n hn
  exact ⟨div_nonneg hr (tangentScale_pos n).le, (div_le_one (tangentScale_pos n)).mpr
    (by unfold tangentScale; linarith)⟩

/-- The ray inherits the speed of its original segment. -/
theorem tangentRay_speed (a : RadialSegment o x) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    dist (tangentRay a r) (tangentRay a s) = dist o x * |r-s| := by
  apply tangent_dist_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [parameter_eventually r hr, parameter_eventually s hs] with n hnr hns
  change _ = tangentScale n * dist (rayValue a r n) (rayValue a s n)
  rw [rayValue, rayValue, ite_eq_left hnr, ite_eq_left hns, a.speed _ hnr _ hns,
    ← sub_div, abs_div, abs_of_pos (tangentScale_pos n)]
  field_simp [(tangentScale_pos n).ne']

/-- The distance between two rays at time `r` is exactly `r` times their
common infinitesimal separation. -/
theorem tangentRay_cross (hT : FractionTransport X) (a : RadialSegment o x) (b : RadialSegment o y)
    {r : ℝ} (hr : 0 ≤ r) : dist (tangentRay a r) (tangentRay b r) = radialSlope a b * r := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · apply tangent_dist_eq_of_tendsto
    simp [tangentRay, rayValue, a.start, b.start]
  let d := dist (tangentRay a r) (tangentRay b r)
  have hd := tangent_dist_tendsto (tangentRay a r) (tangentRay b r)
  let q := fun t ↦ dist (a.path t) (b.path t)/t
  have heq : ∀ᶠ n : ℕ in (tangentFilter : Filter ℕ),
      tangentScale n * dist ((tangentRay a r).point n) ((tangentRay b r).point n) =
      r * q (r / tangentScale n) := by
    filter_upwards [tangentFilter_le_atTop (parameter_eventually r hr.le)] with n ht
    simp only [tangentRay, rayValue, ite_eq_left ht, q]
    field_simp [hr.ne']
  have hlim : Tendsto (fun n ↦ r * q (r / tangentScale n)) tangentFilter (𝓝 d) := hd.congr' heq
  apply le_antisymm
  · rw [← div_le_iff₀ hr]
    apply le_csInf (image_nonempty.mpr (nonempty_Ioc.mpr zero_lt_one))
    rintro _ ⟨t, ht, rfl⟩
    apply (div_le_iff₀ hr).mpr
    apply le_of_tendsto hlim
    have htend : ∀ᶠ n : ℕ in atTop, r / tangentScale n ≤ t := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (r / t)] with n hn
      apply (div_le_iff₀ (tangentScale_pos n)).mpr
      have := (div_le_iff₀ ht.1).mp hn
      unfold tangentScale
      nlinarith only [this, ht.1.le]
    filter_upwards [tangentFilter_le_atTop htend, tangentFilter_le_atTop (parameter_eventually r hr.le)]
      with n hn hi
    exact (mul_le_mul_of_nonneg_left (radial_ratio_mono hT a b ⟨div_pos hr (tangentScale_pos n), hi.2⟩ ht hn)
      hr.le).trans_eq (mul_comm _ _)
  · rw [mul_comm]
    apply ge_of_tendsto hlim
    filter_upwards [tangentFilter_le_atTop (parameter_eventually r hr.le)] with n hn
    exact mul_le_mul_of_nonneg_left (radialSlope_le_ratio a b ⟨div_pos hr (tangentScale_pos n), hn.2⟩) hr.le

end WireGeometry

end VPVNP
end Computability
end OAI
