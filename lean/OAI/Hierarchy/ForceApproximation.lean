import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace OAI
/-! # The force error on the terminal legs of a wire tensor

The supporting forces of a near-optimal summand approximate the prescribed
antipodal wire loads. The estimate is dimension independent and permits legs
of dimension one, whose logarithmic weights vanish. -/

namespace Hierarchy.ForceApproximation

open scoped BigOperators InnerProductSpace
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The summed error certificate in Lemma 3.1 of the low-degree lower bound. -/
theorem sum_norm_sub_le (s : Finset ι) (b : ι → ℝ) (x g : ι → E) (loss : ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hx : ∀ i ∈ s, ‖x i‖ = 1)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ b i)
    (support : (∑ i ∈ s, b i) - loss ≤ ∑ i ∈ s, ⟪g i, x i⟫_ℝ) :
    ∑ i ∈ s, ‖g i - b i • x i‖ ≤ Real.sqrt (2 * (∑ i ∈ s, b i) * loss) := by
  have deficit (i : ι) (hi : i ∈ s) : 0 ≤ b i - ⟪g i, x i⟫_ℝ := by
    have h := real_inner_le_norm (g i) (x i)
    rw [hx i hi, mul_one] at h
    linarith [hg i hi]
  have square (i : ι) (hi : i ∈ s) :
      ‖g i - b i • x i‖ ^ 2 ≤ b i * (2 * (b i - ⟪g i, x i⟫_ℝ)) := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hb i hi), hx i hi, mul_one]
    nlinarith [sq_le_sq' (by linarith [norm_nonneg (g i), hb i hi] : -(b i) ≤ ‖g i‖) (hg i hi)]
  have cs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hb
    (fun i hi => mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (deficit i hi)) square
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at cs
  apply Real.le_sqrt_of_sq_le
  calc
    _ ≤ _ := cs
    _ ≤ (∑ i ∈ s, b i) * (2 * loss) :=
      mul_le_mul_of_nonneg_left (by linarith) (Finset.sum_nonneg hb)
    _ = _ := by ring

/-- The same error controls every prospective cut, even when selected after the summand. -/
theorem cut_load_le {s I : Finset ι} (sub : I ⊆ s) (b : ι → ℝ) (x g : ι → E) (loss rank : ℝ)
    (err : ∑ i ∈ s, ‖g i - b i • x i‖ ≤ loss) (cut : ‖∑ i ∈ I, g i‖ ≤ rank) :
    ‖∑ i ∈ I, b i • x i‖ ≤ rank + loss := by
  calc
    _ = ‖(∑ i ∈ I, g i) - ∑ i ∈ I, (g i - b i • x i)‖ := by rw [Finset.sum_sub_distrib,sub_sub_cancel]
    _ ≤ ‖∑ i ∈ I, g i‖ + ‖∑ i ∈ I, (g i - b i • x i)‖ := norm_sub_le _ _
    _ ≤ rank + ∑ i ∈ I, ‖g i - b i • x i‖ := add_le_add cut (norm_sum_le ..)
    _ ≤ rank + loss := add_le_add_right
      ((Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => norm_nonneg _)).trans err) _

end Hierarchy.ForceApproximation

end OAI
