import OAI.Computability.MultitapeWeakETH.Placement
import OAI.Computability.MultitapeWeakETH.Geometry

/-! # Concentration of pairwise distances in the common placement -/

namespace OAI.Computability.MultitapeWeakETH

open Finset MetricKMedian.PCP VPVNP.SpectralGeometry
open scoped BigOperators

variable {V X : Type} [Fintype V] [Nonempty V] [MetricSpace X]

theorem scalar_variance [DecidableEq V] (A : Matrix V V ℝ) (nonnegative : ∀ i j, 0 ≤ A i j)
    {C : ℝ} (hC : 0 ≤ C) (scalar : HasPoincareBound ℝ A C)
    (p : V → X) (f : V → ℝ) (lip : ∀ i j, |f i - f j| ≤ dist (p i) (p j)) :
    ∑ v, (f v - 𝔼 w, f w)^2 ≤ C * walkEnergy A p := by
  have centered (v) : (f v - 𝔼 w, f w)^2 ≤ 𝔼 w, (f v-f w)^2 := by
    simpa only [energy,expect_sub_distrib,Fintype.expect_const] using
      mean_sq_le_energy (fun w => f v-f w)
  have energyLe : walkEnergy A f ≤ walkEnergy A p := by
    apply sum_le_sum
    intro i _
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ dist_nonneg (lip j i) 2) (nonnegative i j)
  apply (sum_le_sum (s := univ) fun v _ => centered v).trans
  simp only [Fintype.expect_eq_sum_div_card,← sum_div]
  have bound := (scalar f).trans (mul_le_mul_of_nonneg_left energyLe hC)
  simpa only [Real.dist_eq,sq_abs] using bound

theorem distance_mean_lipschitz (p : V → X) (a b : V) :
    |(𝔼 i, dist (p i) (p a)) - 𝔼 i, dist (p i) (p b)| ≤ dist (p a) (p b) := by
  rw [← expect_sub_distrib]
  have point (i : V) : |dist (p i) (p a)-dist (p i) (p b)| ≤ dist (p a) (p b) := by
    rw [dist_comm (p i) (p a),dist_comm (p i) (p b)]
    exact abs_dist_sub_le _ _ _
  apply abs_le.mpr
  constructor
  · simpa only [Fintype.expect_const] using
      (expect_le_expect (s := univ) (fun i _ => (abs_le.mp (point i)).1))
  · simpa only [Fintype.expect_const] using
      (expect_le_expect (s := univ) (fun i _ => (abs_le.mp (point i)).2))

private theorem variance_identity (f : V → ℝ) :
    (𝔼 i, (f i - 𝔼 j, f j)^2) = (𝔼 i, (f i)^2) - (𝔼 i, f i)^2 := by
  simp_rw [sub_sq,expect_add_distrib,expect_sub_distrib,← expect_mul,← mul_expect,Fintype.expect_const]
  ring

/-- If a nonnegative distance is normalized to have second moment one, both
conditional variances together control the distance of its mean from one. -/
theorem mean_distance_deviation (d : V → V → ℝ) (nonnegative : ∀ i j, 0 ≤ d i j)
    (unitMoment : (𝔼 j, 𝔼 i, (d i j)^2) = 1) (ε : ℝ)
    (within : ∀ j, (𝔼 i, (d i j - 𝔼 x, d x j)^2) ≤ ε)
    (between : (𝔼 j, ((𝔼 i, d i j) - 𝔼 y, 𝔼 x, d x y)^2) ≤ ε) :
    ((𝔼 j, 𝔼 i, d i j)-1)^2 ≤ 2*ε := by
  let g (j : V) := 𝔼 i, d i j
  let μ := 𝔼 j, g j
  have within' (j) : (𝔼 i, (d i j)^2) - (g j)^2 ≤ ε := by
    simpa only [variance_identity,g] using within j
  have total := expect_le_expect (s := univ) (fun j _ => within' j)
  rw [expect_sub_distrib,unitMoment,Fintype.expect_const] at total
  have between' : (𝔼 j, (g j)^2) - μ^2 ≤ ε := by
    rw [← variance_identity]; exact between
  have nonnegμ : 0 ≤ μ := expect_nonneg fun j _ => expect_nonneg fun i _ => nonnegative i j
  have square : μ^2 ≤ 1 := calc
    _ ≤ _ := mean_sq_le_energy g
    _ ≤ _ := (expect_le_expect (s := univ) (fun j _ => mean_sq_le_energy (fun i => d i j))).trans
      (le_of_eq unitMoment)
  have leOne : μ ≤ 1 := by nlinarith
  change (μ-1)^2 ≤ _
  nlinarith [mul_nonneg nonnegμ (sub_nonneg.mpr leOne)]

end OAI.Computability.MultitapeWeakETH
