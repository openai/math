import OAI.Computability.VPVNP.CATZeroPoint

/-!
# Equality in CAT(0) comparison along a segment

The difference between the Euclidean comparison quadratic and the squared
distance to a fixed test point is a nonnegative concave function of the
segment parameter. Vanishing at an interior parameter forces it to vanish
along the entire segment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {X : Type*} [MetricSpace X]

private theorem exists_fraction_through (s t : Set.Icc (0 : ℝ) 1)
    (hs₀ : 0 < (s : ℝ)) (hs₁ : (s : ℝ) < 1) :
    ∃ e u : Set.Icc (0 : ℝ) 1, (u : ℝ) < 1 ∧ catFraction t e u = s := by
  by_cases hts : (t : ℝ) ≤ s
  · have ht : 0 < 1 - (t : ℝ) := by linarith
    let e : Set.Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
    let u : Set.Icc (0 : ℝ) 1 := ⟨(s - (t : ℝ)) / (1 - t),
      div_nonneg (sub_nonneg.mpr hts) ht.le,
      (div_le_one ht).mpr (by linarith)⟩
    refine ⟨e, u, (div_lt_one ht).mpr (by linarith), Subtype.ext ?_⟩
    change (1 - ((s : ℝ) - t) / (1 - t)) * t + ((s : ℝ) - t) / (1 - t) * 1 = s
    field_simp [ht.ne']
    ring
  · have ht : 0 < (t : ℝ) := hs₀.trans (lt_of_not_ge hts)
    let e : Set.Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
    let u : Set.Icc (0 : ℝ) 1 := ⟨((t : ℝ) - s) / t,
      div_nonneg (sub_nonneg.mpr (le_of_not_ge hts)) ht.le,
      (div_le_one ht).mpr (by linarith)⟩
    refine ⟨e, u, (div_lt_one ht).mpr (by linarith), Subtype.ext ?_⟩
    change (1 - ((t : ℝ) - s) / t) * t + ((t : ℝ) - s) / t * 0 = s
    field_simp [ht.ne']
    ring

/-- If squared CAT(0) comparison with a fixed vertex is an equality at an
interior point of the opposite side, it is an equality at every point of that side. -/
theorem catPoint_bound_eq_of_interior (h : HasCATZeroSegments X) (a b z : X)
    (s : Set.Icc (0 : ℝ) 1) (hs₀ : 0 < (s : ℝ)) (hs₁ : (s : ℝ) < 1)
    (hs : dist z (catPoint h a b s) ^ 2 =
      (1 - (s : ℝ)) * dist z a ^ 2 + (s : ℝ) * dist z b ^ 2 -
        (s : ℝ) * (1 - s) * dist a b ^ 2)
    (t : Set.Icc (0 : ℝ) 1) :
    dist z (catPoint h a b t) ^ 2 =
      (1 - (t : ℝ)) * dist z a ^ 2 + (t : ℝ) * dist z b ^ 2 -
        (t : ℝ) * (1 - t) * dist a b ^ 2 := by
  let Q (r : ℝ) := (1 - r) * dist z a ^ 2 + r * dist z b ^ 2 -
    r * (1 - r) * dist a b ^ 2
  let deficit (r : Set.Icc (0 : ℝ) 1) := Q r - dist z (catPoint h a b r) ^ 2
  have nonneg (r : Set.Icc (0 : ℝ) 1) : 0 ≤ deficit r :=
    sub_nonneg.mpr (catPoint_bound h a b r z)
  obtain ⟨e, u, hu, he⟩ := exists_fraction_through s t hs₀ hs₁
  have hseg := catPoint_bound h (catPoint h a b t) (catPoint h a b e) u z
  rw [catPoint_subsegment, dist_catPoint_catPoint, mul_pow, sq_abs] at hseg
  have hquadratic : Q (catFraction t e u) =
      (1 - (u : ℝ)) * Q t + (u : ℝ) * Q e -
        (u : ℝ) * (1 - u) * (((t : ℝ) - e) ^ 2 * dist a b ^ 2) := by
    dsimp [Q, catFraction]
    ring
  have hconc : (1 - (u : ℝ)) * deficit t + (u : ℝ) * deficit e ≤ deficit s := by
    rw [← he]
    dsimp only [deficit]
    rw [hquadratic]
    linarith only [hseg]
  have hs' : deficit s = 0 := sub_eq_zero.mpr hs.symm
  rw [hs'] at hconc
  have ht : deficit t ≤ 0 := by
    apply nonpos_of_mul_nonpos_right _ (sub_pos.mpr hu)
    linarith only [hconc, mul_nonneg u.property.1 (nonneg e)]
  exact (sub_eq_zero.mp (le_antisymm ht (nonneg t))).symm

end SpectralGeometry

end VPVNP
end Computability
end OAI
