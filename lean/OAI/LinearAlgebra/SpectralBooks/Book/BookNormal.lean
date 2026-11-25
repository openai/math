import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

/-!
# The outward increment in the three-page construction

Section `sec:book` compares two sphere integrals at an exterior differentiability
point. A strict violation at a test normal persists on a neighborhood of
positive sphere measure. Testing the entire ray of lifted normals then forces
the gradient to have norm one and nonnegative outward component.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Book

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

/-- Removing the region where `h > 0` cannot preserve the integral of a
nonnegative continuous weight at an interior point where that weight is positive. -/
private theorem le_zero_of_integral_comparison {S : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [μ.IsOpenPosMeasure] {A : Set S} {w h : S → ℝ}
    (hw : Continuous w) (hh : Continuous h) (hw0 : ∀ n, 0 ≤ w n)
    (hI : IntegrableOn w A μ)
    (hcmp : ∫ n in A, w n ∂μ ≤ ∫ n in A ∩ {n | h n ≤ 0}, w n ∂μ)
    {n : S} (hn : A ∈ 𝓝 n) (hnw : 0 < w n) : h n ≤ 0 := by
  by_contra! hn'
  have hnear : Function.support w ∩ (A \ {n | h n ≤ 0}) ∈ 𝓝 n := by
    filter_upwards [hn, continuousAt_const.eventually_lt hw.continuousAt hnw,
      continuousAt_const.eventually_lt hh.continuousAt hn'] with x hx hxw hxh
    exact ⟨hxw.ne', hx, not_le.mpr hxh⟩
  have hpos : 0 < ∫ n in A \ {n | h n ≤ 0}, w n ∂μ :=
    (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hw0)
      (hI.mono_set sdiff_subset)).mpr (μ.measure_pos_of_mem_nhds hnear)
  have hsplit := integral_inter_add_sdiff (μ := μ) (s := A)
    (t := {n | h n ≤ 0}) (measurableSet_le hh.measurable measurable_const) hI
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean space of the tangent construction, with one extra coordinate. -/
abbrev Lift (E : Type*) := WithLp 2 (E × ℝ)

/-- The sphere on which the normal cones are measured. -/
abbrev LiftSphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : Lift E) 1

/-- Embed the page in the first coordinates of the tangent construction. -/
def horizontal (v : E) : Lift E := WithLp.toLp 2 (v, 0)

/-- The Euclidean representative of the tangent direction toward the other page. -/
noncomputable def liftedDirection (g : E) (r : ℝ) : Lift E :=
  r • WithLp.toLp 2 (-g, Real.sqrt (1 - ‖g‖ ^ 2))

/-- The Euclidean side of equation `eq:book-tangent`. -/
theorem liftedDirection_dist_sq (g v : E) (r M : ℝ) (hg : ‖g‖ ≤ 1) :
    dist (M • liftedDirection g r) (horizontal v) ^ 2 =
      M ^ 2 * r ^ 2 + ‖v‖ ^ 2 + 2 * M * r * ⟪g, v⟫_ℝ := by
  have hsq : 0 ≤ 1 - ‖g‖ ^ 2 := by nlinarith [norm_nonneg g]
  let u : Lift E := WithLp.toLp 2 (-g, Real.sqrt (1 - ‖g‖ ^ 2))
  have hu : ‖u‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp [u, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hsq]
  have hhor : ‖horizontal v‖ ^ 2 = ‖v‖ ^ 2 := by
    simp [horizontal]
  change dist (M • r • u) (horizontal v) ^ 2 = _
  rw [dist_eq_norm, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_left, mul_pow, mul_pow, hu, hhor]
  simp [u, horizontal, Real.norm_eq_abs, sq_abs]
  ring

/-- The sphere directions in which `y` dominates the common inner cube `K`. -/
def normalCone (K : Set E) (y : E) : Set (LiftSphere E) :=
  {n | ∀ z ∈ K, ⟪(n : Lift E), horizontal (z - y)⟫_ℝ ≤ 0}

/-- The outward width increment per test normal. -/
noncomputable def outwardWeight (e : E) (n : LiftSphere E) : ℝ :=
  max 0 ⟪(n : Lift E), horizontal e⟫_ℝ

/-- The sphere integral comparison in the outward-increment argument forces a
unit gradient with nonnegative component in the outward direction `e`.
Here `r` is the positive distance `f(y)` and `K` can be any compact set
lying strictly below `y` in the `e` direction. -/
theorem unit_gradient_of_outward_integral
    [FiniteDimensional ℝ E] [MeasurableSpace (LiftSphere E)] [BorelSpace (LiftSphere E)]
    (σ : Measure (LiftSphere E)) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    {K : Set E} (hK : IsCompact K) {y e g : E} {r : ℝ}
    (he : ‖e‖ = 1) (hr : 0 < r) (hg : ‖g‖ ≤ 1)
    (hbelow : ∀ z ∈ K, ⟪e, z - y⟫_ℝ < 0)
    (hcmp : ∫ n in normalCone K y, outwardWeight e n ∂σ ≤
      ∫ n in normalCone K y ∩ {n | ⟪(n : Lift E), liftedDirection g r⟫_ℝ ≤ 0},
        outwardWeight e n ∂σ) :
    ‖g‖ = 1 ∧ 0 ≤ ⟪e, g⟫_ℝ := by
  have hweight : Continuous (outwardWeight e) :=
    continuous_const.max (continuous_subtype_val.inner continuous_const)
  have hI := hweight.integrable_of_hasCompactSupport (μ := σ)
    (HasCompactSupport.of_compactSpace _)
  have hray (s : ℝ) :
      -⟪e, g⟫_ℝ + s * Real.sqrt (1 - ‖g‖ ^ 2) ≤ 0 := by
    let v : Lift E := WithLp.toLp 2 (e, s)
    have hv : v ≠ 0 := by
      intro hv
      have he0 : e = 0 := by simpa [v] using congrArg WithLp.fst hv
      simp [he0] at he
    let n : LiftSphere E :=
      ⟨‖v‖⁻¹ • v, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hv)⟩
    have hsc : 0 < ‖v‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hv)
    have htest (z : E) :
        ⟪(n : Lift E), horizontal z⟫_ℝ = ‖v‖⁻¹ * ⟪e, z⟫_ℝ := by
      simp [n, v, horizontal, real_inner_smul_left]
    have hnK : normalCone K y ∈ 𝓝 n := by
      have hnear := hK.eventually_forall_of_forall_eventually
        (x₀ := n) (P := fun a z => ⟪(a : Lift E), horizontal (z - y)⟫_ℝ < 0)
        (fun z hz => by
          have hc : Continuous (fun p : LiftSphere E × E =>
              ⟪(p.1 : Lift E), horizontal (p.2 - y)⟫_ℝ) := by
            unfold horizontal
            fun_prop
          apply hc.continuousAt.eventually_lt continuousAt_const
          exact (htest (z - y)) ▸ mul_neg_of_pos_of_neg hsc (hbelow z hz))
      exact hnear.mono fun a ha z hz => (ha z hz).le
    have hw : 0 < outwardWeight e n := by
      apply lt_of_lt_of_le _ (le_max_right _ _)
      rw [htest, real_inner_self_eq_norm_sq, he]
      simpa using hsc
    have ht := le_zero_of_integral_comparison σ hweight
      (continuous_subtype_val.inner (continuous_const (y := liftedDirection g r)))
      (fun a => le_max_left _ _) hI.integrableOn hcmp hnK hw
    change ⟪‖v‖⁻¹ • v, r • WithLp.toLp 2 (-g, Real.sqrt (1 - ‖g‖ ^ 2))⟫_ℝ ≤ 0 at ht
    rw [real_inner_smul_left, real_inner_smul_right] at ht
    simpa [v, real_inner_comm, mul_comm] using
      (nonpos_of_mul_nonpos_right (nonpos_of_mul_nonpos_right ht hsc) hr)
  have hcomponent : 0 ≤ ⟪e, g⟫_ℝ := by simpa using hray 0
  refine ⟨le_antisymm hg ?_, hcomponent⟩
  by_contra! hsmall
  have hsq : 0 < 1 - ‖g‖ ^ 2 := by nlinarith [norm_nonneg g]
  have hroot := Real.sqrt_pos.mpr hsq
  have hlarge := hray ((⟪e, g⟫_ℝ + 1) / Real.sqrt (1 - ‖g‖ ^ 2))
  rw [div_mul_cancel₀ _ hroot.ne'] at hlarge
  linarith

end Book

end SpectralBooks
end LinearAlgebra
end OAI
