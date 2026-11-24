import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.IsLUB
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Barycenters in the spectral wire geometry

Section 5.3 of *VP and VNP differ over every field* smooths a configuration by
taking barycenters along the rows of a stochastic matrix. In a complete space
satisfying the CAT(0) inequality (4.2), every finite probability distribution
admits a barycenter with the squared-distance variance bound used in that step.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

open Filter Topology

/-- The squared-distance form (4.2) of the CAT(0) geodesic inequality. The
point at fraction `t` along `xy` satisfies the bound for every test point. -/
def HasCATZeroSegments (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ (x y : X) (t : ℝ), 0 ≤ t → t ≤ 1 → ∃ w : X, ∀ z : X,
    dist z w ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 -
      t * (1 - t) * dist x y ^ 2

variable {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]

/-- The mean squared distance to a finite distribution of points. -/
noncomputable def weightedSquaredDistance (mass : ι → ℝ) (points : ι → X) (z : X) : ℝ :=
  ∑ i, mass i * dist (points i) z ^ 2

private theorem energy_segment (h : HasCATZeroSegments X) (mass : ι → ℝ)
    (points : ι → X) (hpos : ∀ i, 0 ≤ mass i) (hsum : ∑ i, mass i = 1)
    (x y : X) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ∃ w : X, weightedSquaredDistance mass points w ≤
      (1 - t) * weightedSquaredDistance mass points x +
        t * weightedSquaredDistance mass points y - t * (1 - t) * dist x y ^ 2 := by
  obtain ⟨w, hw⟩ := h x y t ht ht'
  refine ⟨w, ?_⟩
  calc
    _ ≤ ∑ i, ((1 - t) * (mass i * dist (points i) x ^ 2) +
        t * (mass i * dist (points i) y ^ 2) - mass i * (t * (1 - t) * dist x y ^ 2)) := by
      apply Finset.sum_le_sum
      intro i _
      convert mul_le_mul_of_nonneg_left (hw (points i)) (hpos i) using 1
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.sum_mul, hsum, one_mul]
      rfl

/-- Existence and the variance inequality from Section 5.3. At every test
point the energy exceeds its minimum by at least the squared displacement. -/
theorem exists_barycenter_variance [CompleteSpace X] [Nonempty X] (h : HasCATZeroSegments X)
    (mass : ι → ℝ) (points : ι → X) (hpos : ∀ i, 0 ≤ mass i) (hsum : ∑ i, mass i = 1) :
    ∃ b : X, ∀ z : X, weightedSquaredDistance mass points b + dist b z ^ 2 ≤
      weightedSquaredDistance mass points z := by
  let E := weightedSquaredDistance mass points
  have hE : Continuous E := by unfold E weightedSquaredDistance; fun_prop
  let m := sInf (Set.range E)
  have hbdd : BddBelow (Set.range E) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hpos i) (sq_nonneg _))
  have hlow (z : X) : m ≤ E z := csInf_le hbdd ⟨z, rfl⟩
  obtain ⟨a, _, ha, ha'⟩ := exists_seq_tendsto_sInf (Set.range_nonempty E) hbdd
  choose u hu using ha'
  have hcauchy : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hnear : ∀ᶠ n in atTop, a n < m + ε ^ 2 / 4 :=
      ha.eventually_lt_const (by change m < m + ε ^ 2 / 4; linarith [sq_pos_of_pos hε])
    obtain ⟨N, hN⟩ := eventually_atTop.mp hnear
    refine ⟨N, fun i hi j hj => ?_⟩
    obtain ⟨w, hw⟩ := energy_segment h mass points hpos hsum (u i) (u j) (1 / 2)
      (by norm_num) (by norm_num)
    change E w ≤ _ * E (u i) + _ * E (u j) - _ at hw
    rw [hu i, hu j] at hw
    apply (sq_lt_sq₀ dist_nonneg hε.le).mp
    linarith only [hw, hlow w, hN i hi, hN j hj]
  obtain ⟨b, hub⟩ := cauchySeq_tendsto_of_complete hcauchy
  have huE : E ∘ u = a := funext hu
  have hb : E b = m := tendsto_nhds_unique (hE.continuousAt.tendsto.comp hub)
    (show Tendsto (E ∘ u) atTop (𝓝 m) by rw [huE]; exact ha)
  refine ⟨b, fun z => ?_⟩
  change E b + dist b z ^ 2 ≤ E z
  by_contra! hgap
  obtain ⟨δ, hδ, hδ'⟩ := exists_pos_mul_lt (sub_pos.mpr hgap) (dist b z ^ 2)
  let t := min δ 1
  have ht : 0 < t := lt_min hδ zero_lt_one
  have hsmall : dist b z ^ 2 * t < E b + dist b z ^ 2 - E z :=
    (mul_le_mul_of_nonneg_left (min_le_left δ 1) (sq_nonneg _)).trans_lt hδ'
  obtain ⟨w, hw⟩ := energy_segment h mass points hpos hsum b z t ht.le (min_le_right _ _)
  change E w ≤ _ * E b + _ * E z - _ at hw
  have hneg : E z - E b - (1 - t) * dist b z ^ 2 < 0 := by linarith only [hsmall]
  have hbw : E b ≤ E w := hb.trans_le (hlow w)
  nlinarith only [mul_neg_of_pos_of_neg ht hneg, hw, hbw]

/-- In a metric space the barycenter satisfying the variance bound is unique. -/
theorem existsUnique_barycenter_variance {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    [Nonempty Y] (h : HasCATZeroSegments Y) (mass : ι → ℝ) (points : ι → Y)
    (hpos : ∀ i, 0 ≤ mass i) (hsum : ∑ i, mass i = 1) :
    ∃! b : Y, ∀ z : Y, weightedSquaredDistance mass points b + dist b z ^ 2 ≤
      weightedSquaredDistance mass points z := by
  obtain ⟨b, hb⟩ := exists_barycenter_variance h mass points hpos hsum
  refine ⟨b, hb, fun c hc => ?_⟩
  have hcb := hc b
  rw [dist_comm c b] at hcb
  apply dist_eq_zero.mp
  rw [dist_comm c b]
  nlinarith only [hcb, hb c, dist_nonneg (x := b) (y := c)]

end SpectralGeometry

end VPVNP
end Computability
end OAI
