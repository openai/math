import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic.Linarith

/-!
# Mean width of a finite Euclidean configuration

We use the Gaussian normalization of the manuscript. The first variation when a
site leaves the origin is an integral over the directions supported at the origin.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace Classical

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Support function of a finite nonempty set of sites. -/
def support (S : Finset E) (hS : S.Nonempty) (u : E) : ℝ :=
  S.sup' hS (fun x ↦ ⟪u, x⟫)

theorem support_insert (S : Finset E) (hS : S.Nonempty) (v u : E) :
    support (insert v S) (Finset.insert_nonempty v S) u =
      max ⟪u, v⟫ (support S hS u) :=
  Finset.sup'_insert hS _

theorem support_smul (S : Finset E) (hS : S.Nonempty) (u : E) {a : ℝ} (ha : 0 ≤ a) :
    support (S.image (a • ·)) (hS.image _) u = a * support S hS u := by
  unfold support
  rw [Finset.sup'_image]
  simpa only [Function.comp_apply, real_inner_smul_right] using
    (Finset.apply_sup'_eq_sup'_comp hS (a * ·)
      (fun b c ↦ mul_max_of_nonneg b c ha) (f := fun x ↦ ⟪u, x⟫)).symm

theorem support_nonneg_of_zero_mem {S : Finset E} (h0 : 0 ∈ S) (u : E) :
    0 ≤ support S ⟨0, h0⟩ u := by
  simpa only [support, inner_zero_right] using S.le_sup' (fun x ↦ ⟪u, x⟫) h0

/-- Directions at which the origin supports the given configuration. -/
def normalConeAtZero (S : Finset E) : Set E :=
  {u | ∀ x ∈ S, ⟪u, x⟫ ≤ 0}

theorem mem_normalConeAtZero_iff {S : Finset E} (h0 : 0 ∈ S) (u : E) :
    u ∈ normalConeAtZero S ↔ support S ⟨0, h0⟩ u = 0 := by
  change (∀ x ∈ S, ⟪u, x⟫ ≤ 0) ↔ _
  rw [← Finset.sup'_le_iff ⟨0, h0⟩ (fun x ↦ ⟪u, x⟫)]
  exact ⟨(le_antisymm · (support_nonneg_of_zero_mem h0 u)), Eq.le⟩

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
theorem measurableSet_normalConeAtZero (S : Finset E) : MeasurableSet (normalConeAtZero S) := by
  have heq : normalConeAtZero S = ⋂ x ∈ (S : Set E), {u : E | ⟪u, x⟫ ≤ 0} := by
    ext
    simp [normalConeAtZero]
  rw [heq]
  exact .biInter S.countable_toSet fun x _ ↦
    measurableSet_le (f := fun u : E ↦ ⟪u, x⟫) (by fun_prop) measurable_const

/-- Gaussian mean width, normalized to give a segment its Euclidean length. -/
def meanWidth (S : Finset E) (hS : S.Nonempty) : ℝ :=
  Real.sqrt (2 * Real.pi) * ∫ u, support S hS u ∂stdGaussian E

theorem integrable_support (S : Finset E) (hS : S.Nonempty) :
    Integrable (support S hS) (stdGaussian E) := by
  have heq : support S hS = S.sup' hS (fun x u ↦ ⟪u, x⟫) := by
    funext u
    exact (Finset.sup'_apply hS (fun (x u : E) ↦ ⟪u, x⟫) u).symm
  rw [heq]
  refine Finset.sup'_induction hS _ (p := fun f : E → ℝ ↦ Integrable f (stdGaussian E))
    (fun _ hf _ hg ↦ hf.sup hg) (fun x _ ↦ ?_)
  exact (IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const x

omit [BorelSpace E] in
theorem meanWidth_smul (S : Finset E) (hS : S.Nonempty) {a : ℝ} (ha : 0 ≤ a) :
    meanWidth (S.image (a • ·)) (hS.image _) = a * meanWidth S hS := by
  simp only [meanWidth, support_smul S hS _ ha, integral_const_mul, ← mul_assoc]
  rw [mul_comm (Real.sqrt _)]

/-- The exact width increment upon adjoining a site to a dilation. -/
theorem meanWidth_insert_smul_sub (S : Finset E) (hS : S.Nonempty) (v : E)
    {a : ℝ} (ha : 0 ≤ a) :
    meanWidth (insert v (S.image (a • ·))) (Finset.insert_nonempty _ _) -
      meanWidth (S.image (a • ·)) (hS.image _) =
    Real.sqrt (2 * Real.pi) *
      ∫ u, max (⟪u, v⟫ - a * support S hS u) 0 ∂stdGaussian E := by
  unfold meanWidth
  rw [← mul_sub, ← integral_sub (integrable_support _ _) (integrable_support _ _)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
  simp only [support_insert _ (hS.image _), support_smul S hS u ha]
  rcases le_total ⟪u, v⟫ (a * support S hS u) with h | h
  · simp [max_eq_right h, max_eq_right (sub_nonpos.mpr h)]
  · simp [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]

private theorem tendsto_max_sub_mul (b : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun a : ℝ ↦ max (b - a * s) 0) atTop
      (𝓝 (if s = 0 then max b 0 else 0)) := by
  by_cases h : s = 0
  · simp [h]
  · simp only [h, ite_false]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (b / s)] with a ha
    exact (max_eq_right (sub_nonpos.mpr ((div_le_iff₀ (lt_of_le_of_ne hs (Ne.symm h))).mp ha))).symm

/-- The large-dilation limit in the width-marginal formula, using the equivalent
Gaussian integral of the support function. -/
theorem tendsto_meanWidth_insert_smul_sub {S : Finset E} (h0 : 0 ∈ S) (v : E) :
    Tendsto (fun a : ℝ ↦
      meanWidth (insert v (S.image (a • ·))) (Finset.insert_nonempty _ _) -
        meanWidth (S.image (a • ·)) (Finset.Nonempty.image ⟨0, h0⟩ _)) atTop
      (𝓝 (Real.sqrt (2 * Real.pi) *
        ∫ u in normalConeAtZero S, max ⟪u, v⟫ 0 ∂stdGaussian E)) := by
  have hS : S.Nonempty := ⟨0, h0⟩
  have hv : Integrable (fun u : E ↦ ⟪u, v⟫) (stdGaussian E) :=
    (IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const v
  rw [← integral_indicator (measurableSet_normalConeAtZero S)]
  apply Filter.Tendsto.congr' _ (tendsto_const_nhds.mul
    (tendsto_integral_filter_of_dominated_convergence (fun u : E ↦ max ⟪u, v⟫ 0)
      (μ := stdGaussian E) (F := fun (a : ℝ) u ↦ max (⟪u, v⟫ - a * support S hS u) 0)
      ?_ ?_ (hv.sup (integrable_const 0)) ?_))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    exact (meanWidth_insert_smul_sub S hS v ha).symm
  · exact .of_forall fun a ↦
      ((hv.sub ((integrable_support S hS).const_mul a)).sup (integrable_const 0)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    refine ae_of_all _ fun u ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le_max (sub_le_self _ (mul_nonneg ha (support_nonneg_of_zero_mem h0 u))) le_rfl
  · refine ae_of_all _ fun u ↦ ?_
    simpa only [Set.indicator_apply, mem_normalConeAtZero_iff h0] using
      tendsto_max_sub_mul ⟪u, v⟫ (support_nonneg_of_zero_mem h0 u)

/-- Right derivative at the instant when the added site separates from the origin. -/
theorem hasDerivWithinAt_meanWidth_insert {S : Finset E} (h0 : 0 ∈ S) (v : E) :
    HasDerivWithinAt
      (fun h : ℝ ↦ meanWidth (insert (h • v) S) (Finset.insert_nonempty _ _))
      (Real.sqrt (2 * Real.pi) *
        ∫ u in normalConeAtZero S, max ⟪u, v⟫ 0 ∂stdGaussian E) (Set.Ioi 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope' Set.self_notMem_Ioi]
  apply ((tendsto_meanWidth_insert_smul_sub h0 v).comp tendsto_inv_nhdsGT_zero).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : (0 : ℝ) < h := hh
  have hS : S.Nonempty := ⟨0, h0⟩
  have hmove := meanWidth_smul (insert (h • v) S) (Finset.insert_nonempty _ _)
    (inv_nonneg.mpr hp.le)
  simp only [Finset.image_insert, inv_smul_smul₀ hp.ne'] at hmove
  simp only [Function.comp_apply, slope_def_field, zero_smul, Finset.insert_eq_of_mem h0,
    sub_zero, hmove, meanWidth_smul S hS (inv_nonneg.mpr hp.le)]
  ring

end

end

end SpectralBooks
end LinearAlgebra
end OAI
