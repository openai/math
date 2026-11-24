import OAI.Computability.VPVNP.Barycenter
import Mathlib.Topology.UnitInterval

/-! # Fractional points of CAT(0) segments

The squared-distance comparison of (4.2) determines the point at each
fraction of a segment. These points have constant speed and interpolation
on a subsegment agrees with interpolation on the full segment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

open scoped unitInterval

variable {X : Type*} [MetricSpace X]

/-- The point at fraction `t` on the segment from `a` to `b`. -/
noncomputable def catPoint (h : HasCATZeroSegments X) (a b : X) (t : I) : X :=
  (h a b t t.property.1 t.property.2).choose

theorem catPoint_bound (h : HasCATZeroSegments X) (a b : X) (t : I) (z : X) :
    dist z (catPoint h a b t) ^ 2 ≤ (1 - (t : ℝ)) * dist z a ^ 2 + t * dist z b ^ 2 -
      t * (1 - t) * dist a b ^ 2 :=
  (h a b t t.property.1 t.property.2).choose_spec z

private theorem catPoint_endpoints (h : HasCATZeroSegments X) (a b : X) (t : I) :
    dist a (catPoint h a b t) = (t : ℝ) * dist a b ∧
    dist b (catPoint h a b t) = (1 - (t : ℝ)) * dist a b := by
  let x := catPoint h a b t
  have h₁ : dist a x ≤ (t : ℝ) * dist a b := by
    apply (sq_le_sq₀ dist_nonneg (mul_nonneg t.property.1 dist_nonneg)).mp
    have hab := catPoint_bound h a b t a
    simp only [dist_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] at hab
    dsimp [x]
    linarith only [hab]
  have h₂ : dist b x ≤ (1 - (t : ℝ)) * dist a b := by
    apply (sq_le_sq₀ dist_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) dist_nonneg)).mp
    have hab := catPoint_bound h a b t b
    simp only [dist_self, dist_comm b a, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hab
    dsimp [x]
    linarith only [hab]
  have h₃ := dist_triangle a x b
  rw [dist_comm x b] at h₃
  change dist a x = _ ∧ dist b x = _
  constructor <;> linarith only [h₁, h₂, h₃]

/-- Distance to the initial endpoint. -/
theorem dist_left_catPoint (h : HasCATZeroSegments X) (a b : X) (t : I) :
    dist a (catPoint h a b t) = (t : ℝ) * dist a b :=
  (catPoint_endpoints h a b t).1

/-- Distance to the final endpoint. -/
theorem dist_right_catPoint (h : HasCATZeroSegments X) (a b : X) (t : I) :
    dist b (catPoint h a b t) = (1 - (t : ℝ)) * dist a b :=
  (catPoint_endpoints h a b t).2

@[simp] theorem catPoint_zero (h : HasCATZeroSegments X) (a b : X) :
    catPoint h a b 0 = a := by
  symm
  exact dist_eq_zero.mp (by
    simpa only [Set.Icc.coe_zero, zero_mul] using dist_left_catPoint h a b 0)

@[simp] theorem catPoint_one (h : HasCATZeroSegments X) (a b : X) :
    catPoint h a b 1 = b := by
  symm
  exact dist_eq_zero.mp (by
    simpa only [Set.Icc.coe_one, sub_self, zero_mul] using dist_right_catPoint h a b 1)

/-- Endpoint distances characterize a fractional point uniquely. -/
theorem catPoint_unique (h : HasCATZeroSegments X) (a b : X) (t : I) (z : X)
    (ha : dist z a = (t : ℝ) * dist a b) (hb : dist z b = (1 - (t : ℝ)) * dist a b) :
    z = catPoint h a b t := by
  have hd := catPoint_bound h a b t z
  rw [ha, hb] at hd
  apply dist_eq_zero.mp
  nlinarith only [hd, dist_nonneg (x := z) (y := catPoint h a b t)]

/-- Constant speed along a CAT(0) segment. -/
theorem dist_catPoint_catPoint (h : HasCATZeroSegments X) (a b : X) (s t : I) :
    dist (catPoint h a b s) (catPoint h a b t) = |(s : ℝ) - t| * dist a b := by
  apply le_antisymm
  · apply (sq_le_sq₀ dist_nonneg (mul_nonneg (abs_nonneg _) dist_nonneg)).mp
    have hd := catPoint_bound h a b t (catPoint h a b s)
    rw [dist_comm _ a, dist_comm _ b, dist_left_catPoint, dist_right_catPoint] at hd
    rw [mul_pow, sq_abs]
    linarith only [hd]
  · have hd := abs_dist_sub_le (catPoint h a b s) (catPoint h a b t) a
    rw [dist_comm _ a, dist_comm _ a, dist_left_catPoint, dist_left_catPoint, ← sub_mul,
      abs_mul, abs_of_nonneg dist_nonneg] at hd
    exact hd

/-- Fraction obtained by taking a fraction `u` of the way from `s` to `t`. -/
def catFraction (s t u : I) : I :=
  ⟨(1 - (u : ℝ)) * s + u * t, by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr u.property.2) s.property.1)
        (mul_nonneg u.property.1 t.property.1)
    · have hs := mul_le_mul_of_nonneg_left s.property.2 (sub_nonneg.mpr u.property.2)
      have ht := mul_le_mul_of_nonneg_left t.property.2 u.property.1
      linarith⟩

/-- A segment between two fractional points follows the original segment, including when
the two fractions are in decreasing order. -/
theorem catPoint_subsegment (h : HasCATZeroSegments X) (a b : X) (s t u : I) :
    catPoint h (catPoint h a b s) (catPoint h a b t) u = catPoint h a b (catFraction s t u) := by
  symm
  apply catPoint_unique
  · rw [dist_catPoint_catPoint, dist_catPoint_catPoint]
    have hfrac : (catFraction s t u : ℝ) - s = (u : ℝ) * ((t : ℝ) - s) := by
      change (1 - (u : ℝ)) * s + u * t - s = _
      ring
    rw [hfrac, abs_mul, abs_of_nonneg u.property.1, abs_sub_comm (t : ℝ) s, mul_assoc]
  · rw [dist_catPoint_catPoint, dist_catPoint_catPoint]
    have hfrac : (catFraction s t u : ℝ) - t = (1 - (u : ℝ)) * ((s : ℝ) - t) := by
      change (1 - (u : ℝ)) * s + u * t - t = _
      ring
    rw [hfrac, abs_mul, abs_of_nonneg (sub_nonneg.mpr u.property.2), mul_assoc]

end SpectralGeometry

end VPVNP
end Computability
end OAI
