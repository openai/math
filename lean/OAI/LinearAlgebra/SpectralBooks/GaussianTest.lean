import OAI.LinearAlgebra.SpectralBooks.NormalTail
import Mathlib.Probability.CDF
import Mathlib.Tactic

/-! # Quantile consequences of the Gaussian rectangular bound

The normal tail is the real probability of an upper ray under the standard
normal measure. The quantile is the generalized inverse of its CDF.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

noncomputable section

/-- The lower quantile `Φ⁻¹(p)` of the standard normal distribution. -/
def stdNormalQuantile (p : ℝ) : ℝ := sInf {x : ℝ | p ≤ cdf (gaussianReal 0 1) x}

theorem normalTail_eq_one_sub_cdf (x : ℝ) :
    normalTail x = 1 - cdf (gaussianReal 0 1) x := by
  rw [normalTail, cdf_eq_real, ← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]

theorem normalTail_zero : normalTail 0 = 1 / 2 := by
  let μ := gaussianReal 0 1
  have : NullSingletonClass μ := nullSingletonClass_gaussianReal one_ne_zero
  have hneg : μ.map (fun x : ℝ => -x) = μ := by simp [μ, gaussianReal_map_neg]
  have heq : μ.real (Ioi 0) = μ.real (Iio 0) := calc
    μ.real (Ioi 0) = (μ.map (fun x : ℝ => -x)).real (Ioi 0) := by rw [hneg]
    _ = μ.real (Iio 0) := by
      rw [map_measureReal_apply measurable_neg measurableSet_Ioi]
      congr 1
      ext x
      simp
  have hleft : μ.real (Iio 0) = μ.real (Iic 0) := measureReal_congr Iio_ae_eq_Iic
  have hsum := measureReal_add_measureReal_compl (μ := μ) (s := Iic (0 : ℝ)) measurableSet_Iic
  rw [compl_Iic, probReal_univ] at hsum
  change μ.real (Ioi 0) = 1 / 2
  linarith

/-- The finite Gaussian test, with the zero loads omitted as in the Gaussian corollary. -/
def GaussianBound (m : Fin 3 → ℝ) (L : ℝ) : Prop :=
  ∑ i ∈ Finset.univ.filter (fun i => 0 < m i),
    normalTail (Real.sqrt (2 * Real.log (L / m i))) ≤ 1

theorem gaussianBound_smul_iff {m : Fin 3 → ℝ} {L c : ℝ} (hc : 0 < c) :
    GaussianBound (fun i => c * m i) (c * L) ↔ GaussianBound m L := by
  simp [GaussianBound, mul_div_mul_left _ _ hc.ne', mul_pos_iff_of_pos_left hc]

private theorem normalTail_antitone' : Antitone normalTail :=
  fun _ _ hab => measureReal_mono (Ioi_subset_Ioi hab)

/-- Increasing the rank parameter weakens the Gaussian test. -/
theorem GaussianBound.mono {m : Fin 3 → ℝ} {L U : ℝ} (h : GaussianBound m L)
    (hL : 0 ≤ L) (hLU : L ≤ U) : GaussianBound m U := by
  refine le_trans (Finset.sum_le_sum fun i hi => ?_) h
  have hm := (Finset.mem_filter.mp hi).2
  apply normalTail_antitone'
  obtain rfl | hpos := hL.eq_or_lt
  · simp
  apply Real.sqrt_le_sqrt
  gcongr

/-- Decreasing a set of loads weakens the Gaussian test. In particular this
allows passage from rounded integer widths to the unrounded lower estimates. -/
theorem GaussianBound.lowerLoads {m n : Fin 3 → ℝ} {L : ℝ} (h : GaussianBound n L)
    (hL : 0 < L) (hmn : ∀ i, m i ≤ n i) : GaussianBound m L := by
  unfold GaussianBound at *
  simp only [Finset.sum_filter] at *
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) h
  by_cases hi : 0 < m i
  · rw [ite_eq_left hi, ite_eq_left (hi.trans_le (hmn i))]
    apply normalTail_antitone'
    apply Real.sqrt_le_sqrt
    have hn := hi.trans_le (hmn i)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos hL hn)
      (div_le_div_of_nonneg_left hL.le hi (hmn i))) (by norm_num)
  · rw [ite_eq_right hi]
    split
    · exact normalTail_nonneg _
    · rfl

/-- Fixed-load Gaussian bounds pass to limits of positive rank parameters. -/
theorem gaussianBound_of_tendsto {α : Type*} {f : Filter α} [f.NeBot]
    {m : Fin 3 → ℝ} {v : α → ℝ} {L : ℝ} (hL : L ≠ 0)
    (hv : Filter.Tendsto v f (nhds L)) (h : ∀ᶠ t in f, GaussianBound m (v t)) :
    GaussianBound m L := by
  unfold GaussianBound at *
  apply le_of_tendsto _ h
  apply tendsto_finsetSum
  intro i hi
  have hm := (Finset.mem_filter.mp hi).2
  apply normalTail_continuous.continuousAt.tendsto.comp
  apply Filter.Tendsto.sqrt
  exact Filter.Tendsto.const_mul 2 ((hv.div_const (m i)).log (div_ne_zero hL hm.ne'))

/-- A positive load whose normal tail is at most `1 - p` gives a lower bound
on the ratio of the rank parameter to the load. -/
theorem exp_quantile_le_ratio {p m L : ℝ} (hp : 1 / 2 < p) (hm : 0 < m) (hmL : m ≤ L)
    (h : normalTail (Real.sqrt (2 * Real.log (L / m))) ≤ 1 - p) :
    Real.exp (stdNormalQuantile p ^ 2 / 2) ≤ L / m := by
  let z := Real.sqrt (2 * Real.log (L / m))
  let A := {x : ℝ | p ≤ cdf (gaussianReal 0 1) x}
  have hz : z ∈ A := by
    rw [normalTail_eq_one_sub_cdf] at h
    exact show p ≤ _ by linarith
  have hA : 0 ∈ lowerBounds A := by
    intro x hx
    by_contra! hxneg
    have hle := monotone_cdf (gaussianReal 0 1) hxneg.le
    have hhalf := normalTail_zero
    rw [normalTail_eq_one_sub_cdf] at hhalf
    exact (not_lt_of_ge (show p ≤ 1 / 2 by linarith [show p ≤ _ from hx])) hp
  have hq0 : 0 ≤ stdNormalQuantile p := le_csInf ⟨z, hz⟩ hA
  have hqz : stdNormalQuantile p ≤ z := csInf_le ⟨0, hA⟩ hz
  have hlog := Real.log_nonneg ((one_le_div hm).mpr hmL)
  have hzsq : z ^ 2 = 2 * Real.log (L / m) := Real.sq_sqrt (by positivity)
  calc
    _ ≤ Real.exp (Real.log (L / m)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_le_sq' (by linarith : -z ≤ stdNormalQuantile p) hqz]
    _ = L / m := Real.exp_log (div_pos (hm.trans_le hmL) hm)

/-- The Gaussian test at the three square loads gives the exponential square
constant in the characteristic-wise alternative. -/
theorem gaussian_square_lower_bound {L : ℝ} (hflat : 2 ≤ L)
    (h : GaussianBound (fun _ => 2) L) :
    2 * Real.exp (stdNormalQuantile (2 / 3) ^ 2 / 2) ≤ L := by
  simp [GaussianBound, -Real.sqrt_mul] at h
  have he := exp_quantile_le_ratio (p := 2 / 3) (by norm_num) (by norm_num) hflat (by linarith)
  linarith

/-- The two equal loads in a rectangular shape at exponent two give the
Gaussian bound on each admissible dual weight. -/
theorem gaussian_dual_weight_bound {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : GaussianBound ![1 + t, 2, 1 + t] 2) :
    t ≤ 2 * Real.exp (-(stdNormalQuantile (3 / 4) ^ 2) / 2) - 1 := by
  have hpos : 0 < 1 + t := by linarith
  simp [GaussianBound, -Real.sqrt_mul, Finset.sum_filter, Fin.sum_univ_three, hpos, normalTail_zero] at h
  have he := exp_quantile_le_ratio (p := 3 / 4) (by norm_num) hpos (by linarith : 1 + t ≤ 2)
    (by linarith)
  rw [le_div_iff₀ hpos] at he
  rw [neg_div, Real.exp_neg, ← div_eq_mul_inv]
  linarith [(le_div_iff₀ (Real.exp_pos (stdNormalQuantile (3 / 4) ^ 2 / 2))).2
    (by linarith [mul_comm (1 + t) (Real.exp (stdNormalQuantile (3 / 4) ^ 2 / 2))] :
      (1+t) * Real.exp (stdNormalQuantile (3 / 4) ^ 2 / 2) ≤ 2)]

end

end SpectralBooks
end LinearAlgebra
end OAI
