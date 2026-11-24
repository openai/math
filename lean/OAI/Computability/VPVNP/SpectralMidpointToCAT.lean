import OAI.Computability.VPVNP.Barycenter
import OAI.Computability.VPVNP.FractionalGeodesic
import OAI.Computability.VPVNP.WireGeodesic
import Mathlib.Topology.Order.Compact

/-!
# From midpoint comparison to CAT(0) comparison

Section 4.1 passes from (4.1) to the full geodesic inequality (4.2). Along a
constant-speed segment, subtracting the comparison quadratic from the squared
distance gives a continuous midpoint-convex function that vanishes at both
ends. At a maximum, express its parameter as the midpoint of an interval with
one end at a boundary point. The maximum is then at most half itself.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

open scoped unitInterval
open VPVNP.SpectralGeometry

/-- A continuous midpoint-convex function vanishing at both ends of the unit interval is
nonpositive on the whole interval. -/
private theorem nonpos_of_midpoint_convex {f : I → ℝ} (hf : Continuous f)
    (h₀ : f 0 = 0) (h₁ : f 1 = 0)
    (hm : ∀ s m t : I, (m : ℝ) = ((s : ℝ) + t)/2 → 2 * f m ≤ f s + f t) :
    ∀ t, f t ≤ 0 := by
  obtain ⟨m, _, hmMax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
  have hmax := isMaxOn_univ_iff.mp hmMax
  have hnonpos : f m ≤ 0 := by
    by_cases h : (m : ℝ) ≤ 1/2
    · let r : I := ⟨2 * (m : ℝ), mul_nonneg (by norm_num) m.property.1, by linarith⟩
      have hr := hm 0 m r (by change (m : ℝ) = (0 + 2*(m:ℝ))/2; ring)
      linarith only [hr, h₀, hmax r]
    · let l : I := ⟨2*(m:ℝ)-1, by linarith, by linarith [m.property.2]⟩
      have hl := hm l m 1 (by change (m : ℝ) = (2*(m:ℝ)-1+1)/2; ring)
      linarith only [hl, h₁, hmax l]
  exact fun t ↦ (hmax t).trans hnonpos

variable {X : Type*} [MetricSpace X]

/-- The squared midpoint comparison (4.1) implies the full CAT(0) inequality (4.2). -/
theorem hasCATZeroSegments_of_midpoint (hf : HasFractions X) (hT : FractionTransport X)
    (hm : ∀ x y z m : X, AtFraction x y (1/2) m →
      2 * dist z m ^ 2 + (1/2 : ℝ) * dist x y ^ 2 ≤ dist z x ^ 2 + dist z y ^ 2) :
    HasCATZeroSegments X := by
  intro a b t ht ht'
  have hfrac (x y : X) (s : I) : ∃! w, AtFraction x y (s : ℝ) w := by
    obtain ⟨w, hw⟩ := hf x y s s.property.1 s.property.2
    exact ⟨w, hw, fun u hu ↦ atFraction_unique hT s.property.1 s.property.2 hu hw⟩
  obtain ⟨g, hg₀, hg₁, hg⟩ := exists_constantSpeedSegment hfrac a b
  let u : I := ⟨t, ht, ht'⟩
  refine ⟨g u, fun z ↦ ?_⟩
  let f (s : I) := dist z (g s)^2 - ((1-(s:ℝ)) * dist z a^2 + s * dist z b^2 -
    s * (1-s) * dist a b^2)
  have hcg := continuous_of_constantSpeed a b hg
  have hcf : Continuous f := by dsimp [f]; fun_prop
  have h₀ : f 0 = 0 := by simp [f, hg₀]
  have h₁ : f 1 = 0 := by simp [f, hg₁]
  apply sub_nonpos.mp (nonpos_of_midpoint_convex hcf h₀ h₁ ?_ u)
  intro s m v hmid
  have hgm : AtFraction (g s) (g v) (1/2) (g m) := by
    constructor
    · rw [hg, hg, hmid, show (s:ℝ) - ((s:ℝ)+v)/2 = (1/2)*((s:ℝ)-v) by ring,
        abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      ring
    · rw [hg, hg, hmid, show ((s:ℝ)+v)/2 - v = (1/2)*((s:ℝ)-v) by ring,
        abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      ring
  have h := hm _ _ z _ hgm
  rw [hg, mul_pow, sq_abs] at h
  dsimp only [f]
  rw [hmid]
  linarith only [h]

end WireGeometry

end VPVNP
end Computability
end OAI
