import OAI.LinearAlgebra.SpectralBooks.Width
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-! # Support functions of Minkowski sums and continuity of Gaussian mean width -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory Metric Filter
open scoped RealInnerProductSpace Pointwise Classical

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Support functions add under Minkowski addition of finite configurations. -/
theorem support_add (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) (u : E) :
    support (S + T) (hS.add hT) u = support S hS u + support T hT u := by
  unfold support
  apply le_antisymm
  · apply Finset.sup'_le
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    rw [inner_add_right]
    exact add_le_add (S.le_sup' (fun v ↦ ⟪u, v⟫) hx) (T.le_sup' (fun v ↦ ⟪u, v⟫) hy)
  · obtain ⟨x, hx, ex⟩ := Finset.exists_mem_eq_sup' hS (fun v ↦ ⟪u, v⟫)
    obtain ⟨y, hy, ey⟩ := Finset.exists_mem_eq_sup' hT (fun v ↦ ⟪u, v⟫)
    rw [ex, ey, ← inner_add_right]
    exact (S + T).le_sup' (fun v ↦ ⟪u, v⟫) (Finset.add_mem_add hx hy)

/-- Support function restricted to the unit sphere, with its uniform topology. -/
def sphereSupport (S : Finset E) (hS : S.Nonempty) : C(sphere (0 : E) 1, ℝ) where
  toFun u := support S hS u
  continuous_toFun := Continuous.finset_sup'_apply hS (fun _ _ ↦
    continuous_subtype_val.inner continuous_const)

/-- The continuous functions generating the triangle approximation space. -/
def triangleSupports (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Set C(sphere (0 : E) 1, ℝ) :=
  {f | ∃ a b c : E, f = sphereSupport {a, b, c} (Finset.insert_nonempty _ _)}

theorem sphereSupport_add (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) :
    sphereSupport (S + T) (hS.add hT) = sphereSupport S hS + sphereSupport T hT := by
  ext u
  exact support_add S T hS hT u

theorem sphereSupport_zero : sphereSupport ({0} : Finset E) (Finset.singleton_nonempty _) = 0 := by
  ext u
  simp [sphereSupport, support]

theorem support_smul_direction (S : Finset E) (hS : S.Nonempty) (u : E) {a : ℝ} (ha : 0 ≤ a) :
    support S hS (a • u) = a * support S hS u := by
  unfold support
  simpa only [real_inner_smul_left, Function.comp_def] using
    (Finset.apply_sup'_eq_sup'_comp hS (a * ·)
      (fun b c ↦ mul_max_of_nonneg b c ha) (f := fun x ↦ ⟪u, x⟫)).symm

/-- Adjoining sites in the convex hull preserves the support function. -/
theorem support_union_of_subset_convexHull {S T : Finset E} (hS : S.Nonempty)
    (hT : (T : Set E) ⊆ convexHull ℝ (S : Set E)) (u : E) :
    support (S ∪ T) (hS.mono Finset.subset_union_left) u = support S hS u := by
  have hc : Convex ℝ {v : E | ⟪u, v⟫ ≤ support S hS u} :=
    convex_halfSpace_le (innerSL ℝ u).toLinearMap.isLinear _
  have hbound : (S : Set E) ⊆ {v : E | ⟪u, v⟫ ≤ support S hS u} :=
    fun _ hx ↦ Finset.le_sup' (fun w : E ↦ ⟪u, w⟫) hx
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hbound h
    · exact convexHull_min hbound hc (hT h)
  · apply Finset.sup'_le
    intro x hx
    exact Finset.le_sup' _ (Finset.mem_union_left T hx)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
/-- Adjoining finitely many points in the convex hull preserves mean width. -/
theorem meanWidth_union_of_subset_convexHull {S T : Finset E} (hS : S.Nonempty)
    (hT : (T : Set E) ⊆ convexHull ℝ (S : Set E)) :
    meanWidth (S ∪ T) (hS.mono Finset.subset_union_left) = meanWidth S hS := by
  simp only [meanWidth, funext (support_union_of_subset_convexHull hS hT)]

theorem meanWidth_add (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) :
    meanWidth (S + T) (hS.add hT) = meanWidth S hS + meanWidth T hT := by
  simp only [meanWidth, support_add S T hS hT, integral_add (integrable_support S hS) (integrable_support T hT),
    mul_add]

/-- Uniform error on unit directions bounds the error in Gaussian mean width. -/
theorem abs_meanWidth_sub_le (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) {ε : ℝ}
    (hclose : ∀ u ∈ sphere (0 : E) 1, |support S hS u - support T hT u| ≤ ε) :
    |meanWidth S hS - meanWidth T hT| ≤
      (Real.sqrt (2 * Real.pi) * ∫ u : E, ‖u‖ ∂stdGaussian E) * ε := by
  have pointwise (u : E) : |support S hS u - support T hT u| ≤ ε * ‖u‖ := by
    by_cases hu : u = 0
    · simp [hu, support]
    let w := NormedSpace.normalize u
    have hw : w ∈ sphere (0 : E) 1 := by simp [w, NormedSpace.norm_normalize hu]
    have heq : ‖u‖ • w = u := NormedSpace.norm_smul_normalize u
    calc
      _ = ‖u‖ * |support S hS w - support T hT w| := by
        conv_lhs => rw [← heq]
        rw [support_smul_direction _ _ _ (norm_nonneg u), support_smul_direction _ _ _ (norm_nonneg u),
          ← mul_sub, abs_mul, abs_norm]
      _ ≤ ε * ‖u‖ := (mul_le_mul_of_nonneg_left (hclose w hw) (norm_nonneg u)).trans_eq (mul_comm _ _)
  have integralBound := norm_integral_le_of_norm_le
    (f := fun u ↦ support S hS u - support T hT u)
    ((IsGaussian.integrable_fun_id (μ := stdGaussian E)).norm.const_mul ε)
    (Eventually.of_forall pointwise)
  simp only [Real.norm_eq_abs, integral_const_mul] at integralBound
  rw [meanWidth, meanWidth, ← mul_sub, ← integral_sub (integrable_support S hS) (integrable_support T hT),
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left integralBound (Real.sqrt_nonneg _)).trans_eq (by ring)

end

end SpectralBooks
end LinearAlgebra
end OAI
