import OAI.Computability.VPVNP.SectorSpeeds
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# The pullback seminorm of a spectral sector

In Section 4.1 the speeds of parallel affine segments agree at every
interior base point. The triangle inequality on a small translated triangle
gives subadditivity of the common speed. Reversing and rescaling small
segments gives absolute homogeneity. Moving endpoints towards an interior
point and taking a one-sided limit extends the distance formula to the
entire convex sector, including its boundary.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open Filter Topology

variable {X : Type*} [PseudoMetricSpace X] {D : Set (ℝ × ℝ)} {H : (ℝ × ℝ) → X}

private theorem eventually_interior_step {p : ℝ × ℝ} (hp : p ∈ interior D) (v : ℝ × ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), p + t • v ∈ interior D := by
  have hc : Continuous (fun t : ℝ ↦ p + t • v) := by fun_prop
  have hlim : Tendsto (fun t : ℝ ↦ p + t • v) (𝓝[>] 0) (𝓝 p) := by
    simpa using (hc.continuousWithinAt (s := Set.Ioi 0) (x := 0)).tendsto
  exact hlim (isOpen_interior.mem_nhds hp)

private theorem seminorm_of_sector_speed {p : ℝ × ℝ} (hp : p ∈ interior D)
    (speed : (ℝ × ℝ) → ℝ)
    (hs : ∀ x ∈ interior D, ∀ (v : ℝ × ℝ) (t : ℝ), 0 < t → x + t • v ∈ D →
      dist (H x) (H (x + t • v)) = t * speed v) :
    ∃ P : Seminorm ℝ (ℝ × ℝ), (P : (ℝ × ℝ) → ℝ) = speed := by
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hadd (v w : ℝ × ℝ) : speed (v + w) ≤ speed v + speed w := by
    obtain ⟨t, ht, hv, hvw⟩ := (hpos.and ((eventually_interior_step hp v).and
      (eventually_interior_step hp (v + w)))).exists
    have hpath : p + t • v + t • w = p + t • (v + w) := by module
    have hw := hs (p + t • v) hv w t ht (hpath ▸ interior_subset hvw)
    rw [hpath] at hw
    have htri := dist_triangle (H p) (H (p + t • v)) (H (p + t • (v + w)))
    rw [hs p hp v t ht (interior_subset hv), hw,
      hs p hp (v + w) t ht (interior_subset hvw), ← mul_add] at htri
    exact (mul_le_mul_iff_right₀ ht).mp htri
  have hzero : speed 0 = 0 := by
    have hz := hs p hp 0 1 zero_lt_one (by simpa using interior_subset hp)
    simpa using hz.symm
  have hsmul (r : ℝ) (v : ℝ × ℝ) : speed (r • v) = ‖r‖ * speed v := by
    obtain ⟨t, ht, hv⟩ := (hpos.and (eventually_interior_step hp (r • v))).exists
    have hbase := hs p hp (r • v) t ht (interior_subset hv)
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · have hend : p + t • (r • v) + (-(t * r)) • v = p := by module
      have he := hs (p + t • (r • v)) hv v (-(t * r)) (neg_pos.mpr (mul_neg_of_pos_of_neg ht hr))
        (by rw [hend]; exact interior_subset hp)
      rw [hend, dist_comm, hbase] at he
      rw [Real.norm_eq_abs, abs_of_neg hr]
      apply mul_left_cancel₀ ht.ne'
      linarith only [he]
    · simp [hzero]
    · have he := hs p hp v (t * r) (mul_pos ht hr) (by simpa [mul_smul] using interior_subset hv)
      rw [mul_smul, hbase, mul_assoc] at he
      rw [Real.norm_eq_abs, abs_of_pos hr]
      exact mul_left_cancel₀ ht.ne' he
  exact ⟨Seminorm.of speed hadd hsmul, rfl⟩

private theorem sector_distance_boundary (hD : Convex ℝ D)
    (hH : ∀ {x y}, x ∈ D → y ∈ D → ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 →
      AtFraction (H x) (H y) t (H ((1 - t) • x + t • y)))
    {p : ℝ × ℝ} (hp : p ∈ interior D) (P : Seminorm ℝ (ℝ × ℝ))
    (hi : ∀ x ∈ interior D, ∀ y ∈ D, dist (H x) (H y) = P (y - x))
    {x y : ℝ × ℝ} (hx : x ∈ D) (hy : y ∈ D) :
    dist (H x) (H y) = P (y - x) := by
  let f (t : ℝ) := dist (dist (H x) (H y)) ((1 - t) * P (y - x))
  let g (t : ℝ) := t * (dist (H x) (H p) + dist (H y) (H p))
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ≤ g t := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)]
      with t ht ht'
    have htpos : 0 < t := ht
    have hs : 0 ≤ 1 - t := sub_nonneg.mpr ht'.le
    let u := (1 - t) • x + t • p
    let v := (1 - t) • y + t • p
    have hu : u ∈ interior D := hD.combo_self_interior_mem_interior hx hp hs htpos (by ring)
    have hv : v ∈ interior D := hD.combo_self_interior_mem_interior hy hp hs htpos (by ring)
    have hd := hi u hu v (interior_subset hv)
    have hsub : v - u = (1 - t) • (y - x) := by dsimp [v, u]; module
    rw [hsub, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hs] at hd
    have hxu : dist (H x) (H u) = t * dist (H x) (H p) :=
      (hH hx (interior_subset hp) htpos.le ht'.le).1
    have hyv : dist (H y) (H v) = t * dist (H y) (H p) :=
      (hH hy (interior_subset hp) htpos.le ht'.le).1
    simpa only [f, g, hd, hxu, hyv, mul_add] using dist_dist_dist_le (H x) (H y) (H u) (H v)
  have hcf : Continuous f := by dsimp [f]; fun_prop
  have hcg : Continuous g := by dsimp [g]; fun_prop
  have h0 := le_of_tendsto_of_tendsto hcf.continuousWithinAt.tendsto hcg.continuousWithinAt.tendsto he
  exact dist_le_zero.mp (by simpa [f, g] using h0)

/-- The pullback distances of an affine geodesic parametrization on a convex
sector with nonempty interior are given by a single seminorm on the plane.
The conclusion includes pairs of boundary points. -/
theorem exists_sector_seminorm (hD : Convex ℝ D) (htr : FractionTransport X)
    (hH : ∀ {x y}, x ∈ D → y ∈ D → ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 →
      AtFraction (H x) (H y) t (H ((1 - t) • x + t • y)))
    {p : ℝ × ℝ} (hp : p ∈ interior D) :
    ∃ P : Seminorm ℝ (ℝ × ℝ), ∀ x ∈ D, ∀ y ∈ D, dist (H x) (H y) = P (y - x) := by
  obtain ⟨speed, hs⟩ := exists_sector_speed hD htr hH hp
  obtain ⟨P, hP⟩ := seminorm_of_sector_speed hp speed hs
  have hi (x : ℝ × ℝ) (hx : x ∈ interior D) (y : ℝ × ℝ) (hy : y ∈ D) :
      dist (H x) (H y) = P (y - x) := by
    have hv := hs x hx (y - x) 1 zero_lt_one (by simpa using hy)
    simpa [← hP] using hv
  exact ⟨P, fun _ hx _ hy ↦ sector_distance_boundary hD hH hp P hi hx hy⟩

end WireGeometry

end VPVNP
end Computability
end OAI
