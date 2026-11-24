import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-! # Geodesics from unique fractional points

In Corollary 2.5 of *VP and VNP differ over every field*, fractional points are
characterized by their distances to the two endpoints. Uniqueness for every pair of
endpoints makes these fractional points a constant-speed geodesic.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {X : Type*} [MetricSpace X]

/-- Unique fractional points determine a constant-speed segment between each pair. -/
theorem exists_constantSpeedSegment
    (h : ∀ (a b : X) (t : unitInterval), ∃! z,
      dist a z = (t : ℝ) * dist a b ∧ dist z b = (1 - (t : ℝ)) * dist a b)
    (a b : X) : ∃ g : unitInterval → X, g 0 = a ∧ g 1 = b ∧
      ∀ s t, dist (g s) (g t) = |(s : ℝ) - t| * dist a b := by
  choose g hg using fun t => (h a b t).exists
  have ordered (s t : unitInterval) (hst : (s : ℝ) ≤ t) :
      dist (g s) (g t) = ((t : ℝ) - s) * dist a b := by
    rcases lt_or_eq_of_le hst with hlt | heq
    · have ht : (t : ℝ) ≠ 0 := ne_of_gt (lt_of_le_of_lt s.property.1 hlt)
      let u : unitInterval := ⟨(s : ℝ) / t, unitInterval.div_mem s.property.1 t.property.1 hst⟩
      obtain ⟨z, hl, hr⟩ := (h a (g t) u).exists
      have hzleft : dist a z = (s : ℝ) * dist a b := by
        rw [hl, (hg t).1]
        change (s : ℝ) / t * ((t : ℝ) * _) = _
        field_simp
      have hzstep : dist z (g t) = ((t : ℝ) - s) * dist a b := by
        rw [hr, (hg t).1]
        change (1 - (s : ℝ) / t) * ((t : ℝ) * _) = _
        field_simp
      have hzright : dist z b = (1 - (s : ℝ)) * dist a b := by
        have upper := dist_triangle z (g t) b
        rw [hzstep, (hg t).2] at upper
        have lower := dist_triangle a z b
        rw [hzleft] at lower
        linarith only [upper, lower]
      rwa [(h a b s).unique ⟨hzleft, hzright⟩ (hg s)] at hzstep
    · have : s = t := Subtype.ext heq
      subst t
      simp
  refine ⟨g, ?_, ?_, fun s t => ?_⟩
  · exact (eq_of_dist_eq_zero (by simpa using (hg 0).1)).symm
  · exact eq_of_dist_eq_zero (by simpa using (hg 1).2)
  · rcases le_total (s : ℝ) (t : ℝ) with hst | hts
    · rw [ordered s t hst, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
    · rw [dist_comm, ordered t s hts, abs_of_nonneg (sub_nonneg.mpr hts)]

/-- Any two constant-speed segments with these endpoints agree at every parameter. -/
theorem existsUnique_constantSpeedSegment
    (h : ∀ (a b : X) (t : unitInterval), ∃! z,
      dist a z = (t : ℝ) * dist a b ∧ dist z b = (1 - (t : ℝ)) * dist a b)
    (a b : X) : ∃! g : unitInterval → X, g 0 = a ∧ g 1 = b ∧
      ∀ s t, dist (g s) (g t) = |(s : ℝ) - t| * dist a b := by
  have atFraction (g : unitInterval → X) (hg₀ : g 0 = a) (hg₁ : g 1 = b)
      (hg : ∀ s t, dist (g s) (g t) = |(s : ℝ) - t| * dist a b) (t : unitInterval) :
      dist a (g t) = (t : ℝ) * dist a b ∧ dist (g t) b = (1 - (t : ℝ)) * dist a b := by
    constructor
    · simpa [hg₀, abs_of_nonneg t.property.1] using hg 0 t
    · simpa [hg₁, abs_sub_comm (t : ℝ) 1, abs_of_nonneg (sub_nonneg.mpr t.property.2)]
        using hg t 1
  obtain ⟨g, hg₀, hg₁, hg⟩ := exists_constantSpeedSegment h a b
  refine ⟨g, ⟨hg₀, hg₁, hg⟩, fun f ⟨hf₀, hf₁, hf⟩ => ?_⟩
  exact funext fun t => (h a b t).unique (atFraction f hf₀ hf₁ hf t) (atFraction g hg₀ hg₁ hg t)

/-- A constant-speed segment is Lipschitz, hence continuous. -/
theorem continuous_of_constantSpeed (a b : X) {g : unitInterval → X}
    (h : ∀ s t, dist (g s) (g t) = |(s : ℝ) - t| * dist a b) : Continuous g := by
  apply (LipschitzWith.continuous (K := nndist a b))
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist (g s) (g t) ≤ dist a b * dist (s : ℝ) (t : ℝ)
  rw [h, Real.dist_eq, mul_comm]

end SpectralGeometry

end VPVNP
end Computability
end OAI
