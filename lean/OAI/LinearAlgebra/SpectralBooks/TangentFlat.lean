import OAI.LinearAlgebra.SpectralBooks.AxisSites
import OAI.LinearAlgebra.SpectralBooks.AxisRigidity
import OAI.LinearAlgebra.SpectralBooks.ConeFlat
import OAI.LinearAlgebra.SpectralBooks.TangentAxes

/-!
# The Euclidean flat forced by the marked-site inequality

The marked sites are the origin and the signed standard basis vectors.
When the maximal stretch of a nonconstant placement is bounded by the
average stretch of its diameters, the completed CAT(0) tangent cone at its
origin contains an isometric Euclidean space of the prescribed dimension.
This is the metric conclusion in Lemma `axis-rigidity`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction Crossing

/-- The sum of the wire distances of the `D` diameters, i.e. the price
of the crossing tensor with one bit on each wire. -/
def diameterSum {D : ℕ} {X : Type*} [MetricSpace X] (y : AxisSite D → X) : ℝ :=
  ∑ i, dist (y (some (i, false))) (y (some (i, true)))

private theorem origin_dist_axisPoint {D : ℕ} (i : Fin D) (b : Bool) :
    dist (axisPoint none) (axisPoint (some (i, b))) = 1 := by
  cases b <;> simp [axisPoint]

private theorem dist_axisPoint_of_ne {D : ℕ} {i j : Fin D} (hij : i ≠ j) (a b : Bool) :
    dist (axisPoint (some (i, a))) (axisPoint (some (j, b))) = Real.sqrt 2 := by
  apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by norm_num), dist_eq_norm, norm_sub_sq_real]
  cases a <;> cases b <;> norm_num [axisPoint, EuclideanSpace.inner_single_left, hij]

/-- Rigidity with the original diameter-average factor. The nonconstant
placement hypothesis follows in a normalized spectral space from the tree
bound and the positive price of the full diagonal. -/
theorem exists_tangent_flat_of_diameter_average {X : Type*} [MetricSpace X] (h : CATZero X)
    {D : ℕ} (hD : 0 < D) (y : AxisSite D → X)
    (hpos : ∃ p q, 0 < dist (y p) (y q))
    (hcontract : ∀ p q, dist (y p) (y q) ≤
      diameterSum y / (2 * D) * dist (axisPoint p) (axisPoint q)) :
    ∃ f : EuclideanSpace ℝ (Fin D) → TangentCone h (y none), Isometry f := by
  let r := diameterSum y / (2 * D)
  obtain ⟨p, q, hpq⟩ := hpos
  have hr : 0 < r := by
    by_contra! hr
    exact (not_le_of_gt hpq) ((hcontract p q).trans (mul_nonpos_of_nonpos_of_nonneg hr dist_nonneg))
  have hD' : 0 < (D : ℝ) := by exact_mod_cast hD
  let x (i : Fin D) (a : Bool) := y (some (i, a))
  have hradius (i : Fin D) (a : Bool) : dist (y none) (x i a) ≤ r := by
    simpa only [origin_dist_axisPoint, mul_one, x, r] using hcontract none (some (i, a))
  have hsum : ∑ i, dist (x i false) (x i true) = 2 * r * D := by
    change diameterSum y = 2 * (diameterSum y / (2 * D)) * D
    field_simp
  obtain ⟨hd, hrad⟩ := axis_diameters_and_radii_of_sum (y none) x hradius hsum
  have hc (i j : Fin D) (hij : i ≠ j) (a b : Bool) : dist (x i a) (x j b) ≤ r * Real.sqrt 2 := by
    simpa only [dist_axisPoint_of_ne hij, x, r] using hcontract (some (i, a)) (some (j, b))
  obtain ⟨hn, hop, horth⟩ := axisLogs_orthogonal_of_radius h (y none) x hr.le hrad hd hc
  let T := TangentCone.coneData h (y none)
  let v (i : Fin D) (b : Bool) := TangentCone.log h (y none) (x i b)
  let u (i : Fin D) (b : Bool) := T.scale r⁻¹ (v i b)
  have hrinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  have hu (i : Fin D) (b : Bool) : T.normSq (u i b) = 1 := by
    change T.normSq (T.scale r⁻¹ (v i b)) = 1
    rw [T.normSq_scale hrinv, show T.normSq (v i b) = r ^ 2 from hn i b]
    field_simp
  apply exists_isometry_of_orthogonal_axes T (TangentCone.catZero h (y none)) u hu
  · intro i
    refine ⟨(hu i false).trans (hu i true).symm, ?_⟩
    change T.pairing (T.scale r⁻¹ (v i false)) (T.scale r⁻¹ (v i true)) = -T.normSq (u i false)
    rw [T.pairing_scale hrinv hrinv, (hop i).2, hu, hn]
    field_simp
  · intro i j hij a b
    change T.pairing (T.scale r⁻¹ (v i a)) (T.scale r⁻¹ (v j b)) = 0
    rw [T.pairing_scale hrinv hrinv, show T.pairing (v i a) (v j b) = 0 from horth i j hij a b]
    ring

/-- The strict pairwise witness used before the compactness step of the
characteristic-wise alternative. -/
private theorem exists_endpoints_of_no_tangent_flat {X : Type*} [MetricSpace X] (h : CATZero X)
    {D : ℕ} (hD : 0 < D) (y : AxisSite D → X)
    (hpos : ∃ p q, 0 < dist (y p) (y q))
    (hmissing : ¬ ∃ f : EuclideanSpace ℝ (Fin D) → TangentCone h (y none), Isometry f) :
    ∃ p q : AxisSite D, p ≠ q ∧ diameterSum y <
      (2 * D / dist (axisPoint p) (axisPoint q)) * dist (y p) (y q) := by
  classical
  by_contra! hnone
  apply hmissing
  apply exists_tangent_flat_of_diameter_average h hD y hpos
  intro p q
  by_cases he : p = q
  · simp [he]
  have hsep : 0 < dist (axisPoint p) (axisPoint q) :=
    dist_pos.mpr fun heq => he (axisPoint_injective D heq)
  have hd : 0 < 2 * (D : ℝ) := by positivity
  have hp := hnone p q he
  rw [div_mul_eq_mul_div, div_le_iff₀ hsep, mul_comm (2 * (D : ℝ))] at hp
  rwa [div_mul_eq_mul_div, le_div_iff₀ hd]

/-- At least one unordered candidate wire has greater spectral price per unit
length than the average on the diameters, when the tangent flat is missing. -/
theorem exists_pair_of_no_tangent_flat {X : Type*} [MetricSpace X] (h : CATZero X)
    {D : ℕ} (hD : 0 < D) (y : AxisSite D → X)
    (hpos : ∃ p q, 0 < dist (y p) (y q))
    (hmissing : ¬ ∃ f : EuclideanSpace ℝ (Fin D) → TangentCone h (y none), Isometry f) :
    ∃ e : AxisPair D, diameterSum y < (2 * D / axisLength e) *
      dist (y e.val.out.1) (y e.val.out.2) := by
  obtain ⟨p, q, hpq, hlt⟩ := exists_endpoints_of_no_tangent_flat h hD y hpos hmissing
  let e : AxisPair D := ⟨Sym2.mk p q, by simpa using hpq⟩
  have he : Sym2.mk e.val.out.1 e.val.out.2 = Sym2.mk p q := by
    rw [Sym2.mk, Prod.mk.eta, e.val.out_eq]
  have hp := (Sym2.mk_eq_mk_iff (p := e.val.out) (q := (p, q))).1 he
  refine ⟨e, ?_⟩
  rcases hp with hp | hp
  · simpa only [axisLength, hp] using hlt
  · simpa only [axisLength, hp, Prod.swap, dist_comm (axisPoint q) (axisPoint p),
      dist_comm (y q) (y p)] using hlt

end SpectralBooks
end LinearAlgebra
end OAI
