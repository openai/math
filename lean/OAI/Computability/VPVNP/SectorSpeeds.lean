import OAI.Computability.VPVNP.WireGeodesic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Directional speeds on an affine sector

In Section 4.1 of *VP and VNP differ over every field*, the sector map takes
affine segments to constant-speed geodesics. The distance per unit step in
a direction is independent of the step length. Fraction transport toward a
point beyond a second interior base point shows that the speed is independent
of the base point as well.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open Set
open scoped Topology

variable {D : Set (ℝ × ℝ)} {X : Type*} [PseudoMetricSpace X] {H : (ℝ × ℝ) → X}

/-- A sufficiently short positive step from an interior point stays in the domain. -/
theorem exists_positive_step_mem {p : ℝ × ℝ} (hp : p ∈ interior D) (v : ℝ × ℝ) :
    ∃ t : ℝ, 0 < t ∧ p + t • v ∈ D := by
  have hc : Continuous (fun t : ℝ ↦ p + t • v) := by fun_prop
  have hN : (fun t : ℝ ↦ p + t • v) ⁻¹' D ∈ 𝓝 0 := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using mem_interior_iff_mem_nhds.mp hp
  obtain ⟨r, hr, hrD⟩ := exists_Ico_subset_of_mem_nhds hN (exists_gt 0)
  exact ⟨r / 2, by linarith, hrD ⟨by linarith, by linarith⟩⟩

variable (hD : Convex ℝ D) (ht : FractionTransport X)
  (hH : ∀ {x y}, x ∈ D → y ∈ D → ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 →
    AtFraction (H x) (H y) t (H ((1 - t) • x + t • y)))

private def RadialSpeedAt (D : Set (ℝ × ℝ)) (H : (ℝ × ℝ) → X) (p v : ℝ × ℝ) (a : ℝ) : Prop :=
  ∀ (t : ℝ), 0 < t → p + t • v ∈ D → dist (H p) (H (p + t • v)) = t * a

include hH in
private theorem radial_distance_mul {p v : ℝ × ℝ} (hp : p ∈ D) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (hy : p + t • v ∈ D) :
    t * dist (H p) (H (p + s • v)) = s * dist (H p) (H (p + t • v)) := by
  have htpos : 0 < t := hs.trans_le hst
  have hr := (hH hp hy (div_nonneg hs.le htpos.le) ((div_le_one htpos).mpr hst)).1
  have heq : (1 - s / t) • p + (s / t) • (p + t • v) = p + s • v := by
    match_scalars <;> field_simp
    all_goals ring
  rw [heq] at hr
  rw [hr]
  field_simp

include hH in
private theorem exists_local_speed {p : ℝ × ℝ} (hp : p ∈ interior D) (v : ℝ × ℝ) :
    ∃ a, RadialSpeedAt D H p v a := by
  obtain ⟨r, hr, hrD⟩ := exists_positive_step_mem hp v
  refine ⟨dist (H p) (H (p + r • v)) / r, fun t ht' htv ↦ ?_⟩
  rw [← mul_div_assoc, eq_div_iff hr.ne']
  rcases le_total t r with h | h
  · simpa only [mul_comm (dist _ _) r] using radial_distance_mul hH (interior_subset hp) ht' h hrD
  · simpa only [mul_comm (dist _ _) r] using
      (radial_distance_mul hH (interior_subset hp) hr h htv).symm

include hD ht hH in
private theorem radial_speed_le {p q v : ℝ × ℝ} (hp : p ∈ interior D) (hq : q ∈ interior D)
    {a b : ℝ} (ha : RadialSpeedAt D H p v a) (hb : RadialSpeedAt D H q v b) : b ≤ a := by
  obtain ⟨r, hr, hrv⟩ := exists_positive_step_mem hp v
  obtain ⟨e, he, hze⟩ := exists_positive_step_mem hq (q - p)
  let z := q + e • (q - p)
  let k : ℝ := (1 + e)⁻¹
  have hden : 0 < 1 + e := by linarith
  have hk : 0 < k := inv_pos.mpr hden
  have hk' : k < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hqeq : (1 - k) • p + k • z = q := by
    dsimp [z, k]
    match_scalars <;> field_simp
    all_goals ring
  have hveq : (1 - k) • (p + r • v) + k • z = q + ((1 - k) * r) • v := by
    rw [← hqeq]
    module
  have hmem : q + ((1 - k) * r) • v ∈ D := hveq ▸
    hD hrv hze (sub_nonneg.mpr hk'.le) hk.le (by ring)
  have h := ht hk.le hk'.le (hH (interior_subset hp) hze hk.le hk'.le)
    (hH hrv hze hk.le hk'.le)
  rw [hqeq, hveq, dist_self, mul_zero, add_zero, ha r hr hrv,
    hb ((1 - k) * r) (mul_pos (sub_pos.mpr hk') hr) hmem, ← mul_assoc] at h
  exact (mul_le_mul_iff_right₀ (mul_pos (sub_pos.mpr hk') hr)).mp h

include hD ht hH in
/-- A single directional speed applies to all positive steps from all interior
base points, including steps that end on the boundary of the domain. -/
theorem exists_sector_speed {p : ℝ × ℝ} (hp : p ∈ interior D) :
    ∃ speed : (ℝ × ℝ) → ℝ, ∀ x ∈ interior D, ∀ (v : ℝ × ℝ) (t : ℝ),
      0 < t → x + t • v ∈ D → dist (H x) (H (x + t • v)) = t * speed v := by
  choose speed hs using fun v ↦ exists_local_speed hH hp v
  refine ⟨speed, fun x hx v t ht' htv ↦ ?_⟩
  obtain ⟨b, hb⟩ := exists_local_speed hH hx v
  have heq : b = speed v := le_antisymm (radial_speed_le hD ht hH hp hx (hs v) hb)
    (radial_speed_le hD ht hH hx hp hb (hs v))
  rw [← heq]
  exact hb t ht' htv

end WireGeometry

end VPVNP
end Computability
end OAI
