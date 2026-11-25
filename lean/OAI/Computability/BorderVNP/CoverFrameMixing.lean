import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# The analytic steps in finite frame mixing

In the Hecke correspondence of Lemma 5.2, the individual branch values depend
on a choice of representative. Only the sum and the sum of squares need to be
continuous on the quotient. The variance identity forces every branch of a
stationary harmonic function to have the same value. Cesàro averaging then
converges in the uniform norm by compactness and telescoping.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CoverFrameMixing

open Filter Finset MeasureTheory Set
open scoped Topology

/-- A stationary finite correspondence fixes a harmonic function on every branch.
The assumptions concern the two symmetric sums that descend to the quotient. -/
theorem branch_eq_of_stationary {X I : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [Fintype I]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (f : X → ℝ) (branch : X → I → ℝ) (hf : Continuous f)
    (hmean : ∀ x, ∑ i, branch x i = (Fintype.card I : ℝ) * f x)
    (hsecond : Continuous (fun x => ∑ i, (branch x i)^2))
    (hstationary : (∫ x, ∑ i, (branch x i)^2 ∂μ) =
      ∫ x, (Fintype.card I : ℝ) * (f x)^2 ∂μ) (x : X) (i : I) :
    branch x i = f x := by
  let gap (t : X) := (∑ j, (branch t j)^2) - (Fintype.card I : ℝ) * (f t)^2
  have hgap (t : X) : gap t = ∑ j, (branch t j - f t)^2 := by
    simp only [gap, sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul,
      ← mul_sum, sum_const, card_univ, nsmul_eq_mul, hmean]
    ring
  have hn : 0 ≤ gap := fun t => by rw [hgap]; positivity
  have hc : Continuous gap := hsecond.sub (continuous_const.mul (hf.pow 2))
  have hInt : ∫ t, gap t ∂μ = 0 := by
    rw [show gap = (fun t => (∑ j, (branch t j)^2) - (Fintype.card I : ℝ) * (f t)^2) from rfl,
      integral_sub, hstationary, sub_self]
    · exact hsecond.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact (continuous_const.mul (hf.pow 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hx : gap x = 0 := by
    by_contra hne
    exact (integral_pos_of_integrable_nonneg_nonzero hc
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hn hne).ne'
      hInt
  have hi := single_le_sum (f := fun j => (branch x j - f x)^2)
    (fun j _ => sq_nonneg _) (mem_univ i)
  rw [← hgap, hx] at hi
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cesàro average of the first positive number of iterates, starting with the identity. -/
noncomputable def mean (P : E →L[ℝ] E) (f : E) (n : ℕ) : E :=
  ((n : ℝ) + 1)⁻¹ • ∑ j ∈ range (n + 1), P^[j] f

private theorem sum_displace (P : E →L[ℝ] E) (f : E) (n : ℕ) :
    P (∑ j ∈ range n, P^[j] f) - ∑ j ∈ range n, P^[j] f = P^[n] f - f := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sum_range_succ, map_add, Function.iterate_succ_apply' P]
    rw [show P (∑ j ∈ range n, P^[j] f) = (P^[n] f - f) + ∑ j ∈ range n, P^[j] f from
      sub_eq_iff_eq_add.mp ih]
    abel

/-- Telescoping gives the difference of the last and first iterates divided by length. -/
theorem mean_displacement (P : E →L[ℝ] E) (f : E) (n : ℕ) :
    P (mean P f n) - mean P f n = ((n : ℝ) + 1)⁻¹ • (P^[n+1] f - f) := by
  rw [mean, map_smul, ← smul_sub, sum_displace]

private theorem iter_bound (P : E →L[ℝ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (f : E) (n : ℕ) :
    ‖P^[n] f‖ ≤ ‖f‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hP _).trans ih

/-- A contraction has asymptotically fixed Cesàro averages. -/
theorem mean_asymptotically_fixed (P : E →L[ℝ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (f : E) :
    Tendsto (fun n => P (mean P f n) - mean P f n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (g := fun n : ℕ => ((n : ℝ) + 1)⁻¹ * (‖f‖ + ‖f‖))
    (fun _ => norm_nonneg _)
  · intro n
    rw [mean_displacement, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
      (add_le_add (iter_bound P hP f (n+1)) le_rfl)) (by positivity)
  · simpa [mul_comm] using ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
      (tendsto_const_nhds (x := (1 : ℝ)))).inv_tendsto_atTop.const_mul (‖f‖ + ‖f‖)

/-- A continuous invariant statistic selects the limit of relatively compact
Cesàro averages. In the frame-space application the statistic is integration. -/
theorem mean_tendsto (P : E →L[ℝ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (A : E →L[ℝ] ℝ) (hA : ∀ x, A (P x) = A x) (f g : E)
    (hcompact : IsCompact (closure (range (mean P f))))
    (hfixed : ∀ x, P x = x → A x = A f → x = g) :
    Tendsto (mean P f) atTop (𝓝 g) := by
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n => subset_closure (mem_range_self n))
  intro x _ hx
  obtain ⟨s, hs, hlim⟩ := hx.tendsto_subseq
  apply hfixed
  · have lim := ((P.continuous.continuousAt.tendsto.comp hlim).sub hlim)
    have lim0 := (mean_asymptotically_fixed P hP f).comp hs.tendsto_atTop
    exact sub_eq_zero.mp (tendsto_nhds_unique lim lim0)
  · have hiter (j : ℕ) : A (P^[j] f) = A f := by
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', hA, ih]
    have hav (n : ℕ) : A (mean P f n) = A f := by
      simp [mean, map_smul, map_sum, hiter, smul_eq_mul, inv_mul_cancel_left₀ (by positivity : (n:ℝ)+1≠0)]
    apply tendsto_nhds_unique (A.continuous.continuousAt.tendsto.comp hlim)
    simp [Function.comp_def, hav]

end CoverFrameMixing

end BorderVNP
end Computability
end OAI
