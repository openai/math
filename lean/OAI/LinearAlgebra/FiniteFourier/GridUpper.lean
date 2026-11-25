import OAI.LinearAlgebra.FiniteFourier.FactorCosts
import OAI.LinearAlgebra.FiniteFourier.GridUniform
import OAI.LinearAlgebra.FiniteFourier.GridAssembly
import OAI.LinearAlgebra.FiniteFourier.SmallGridCost
import OAI.LinearAlgebra.FiniteFourier.GroupGridBounds
import OAI.LinearAlgebra.FiniteFourier.IntegralGridInputs

/-! # The geometric-grid upper bound from the two companion estimates -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter
universe u v

/-- The geometric grid theorem, conditional only on the two field-uniform
companion circuit estimates. Its constant depends on the target exponent. -/
theorem UniformGridInputs.gridUpper (h : UniformGridInputs.{v}) : UniformGridUpper.{v} := by
  apply uniformGridUpper_of_eventually
  intro α hα
  obtain ⟨β, hhalf, hmin⟩ := exists_between (lt_min hα (by norm_num : (1/2 : ℝ) < 1))
  obtain ⟨hβα, hβ₁⟩ := lt_min_iff.mp hmin
  have hβ : 0 ≤ β := by linarith
  obtain ⟨C, hC, hK⟩ := h β hhalf hβ₁
  obtain ⟨D, hD, hsmall⟩ := eventually_smallGridCost.{v} hβ hβ₁.le hβα hC
  let M := max (7 * C) D
  have hM : 0 < M := hD.trans_le (le_max_right ..)
  refine ⟨25 * M, by positivity, ?_⟩
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℕ)] with N hsmall hN
  intro K _ ι _ _ a A ha hA hvol
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hlog := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hn
  have hbase : 1 ≤ 1 + Real.logb 2 N := by linarith
  have hp : 0 ≤ (1 + Real.logb 2 N) ^ α := Real.rpow_nonneg (by linarith) _
  let B := M * N * (1 + Real.logb 2 N) ^ α
  have hlarge (i : ι) : (Fintype.card (∀ j : {j // j ≠ i}, Fin (a j.val)) : ℝ) *
      complexity (A i) ≤ B := by
    have h₁ := axis_fiber_cost_of_convolution A hβ hC.le (hK K).1
      (fun j ↦ (ha j).trans_lt' (by decide : 0 < 2)) i (hA i)
    rw [Nat.cast_mul, hvol] at h₁
    apply h₁.trans
    dsimp [B]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (le_max_left ..) (Nat.cast_nonneg N)
    · exact Real.rpow_le_rpow_of_exponent_le hbase hβα.le
    · exact Real.rpow_nonneg (by linarith) _
    · positivity
  have hsmall' (S : Finset ι)
      (hB : (∏ i : S, a i.val) ^ 12 ≤ N) :
      (complexity (Matrix.blockDiagonal (fun _ : Fin (N / (∏ i : S, a i.val)) ↦
        gridTensor (fun i : S ↦ A i.val))) : ℝ) ≤ B := by
    have h₁ := hsmall K S (fun i ↦ a i.val) (fun i ↦ A i.val) (hK K).1 (hK K).2
      (fun i ↦ ha i.val) (fun i ↦ hA i.val) hB
    exact h₁.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right ..) (Nat.cast_nonneg N)) hp)
  have hgrid := complexity_gridTensor_of_batch_bounds A hN (show 0 ≤ B by dsimp [B]; positivity)
    (by simpa only [Fintype.card_fin] using hvol)
    (fun i ↦ by simpa only [Fintype.card_fin] using (show 0 < a i by have := ha i; omega))
    (fun i _ ↦ hlarge i)
    (fun S _ hb ↦ by
      have heq : (∏ i : S, Fintype.card (Fin (a i.val))) = ∏ i : S, a i.val := by simp
      have replace (d : ℕ) (hd : d = ∏ i : S, a i.val) :
          (complexity (Matrix.blockDiagonal (fun _ : Fin (N / d) ↦
            gridTensor (fun i : S ↦ A i.val))) : ℝ) ≤ B := by
        subst d
        exact hsmall' S (heq ▸ hb)
      exact replace _ heq)
  exact hgrid.trans_eq (by dsimp [B]; ring)

/-- Character transforms over arbitrary admissible fields satisfy the uniform
upper estimate whenever the two field-uniform companion estimates hold. -/
theorem UniformGridInputs.fourierUpper (h : UniformGridInputs.{v}) : UniformFourierUpper.{u,v} :=
  uniformFourierUpper_of_grid h.gridUpper

/-- The integral convolution and tensor-shear circuits of the companion article
give the Fourier upper bound simultaneously in every characteristic. -/
theorem uniformFourierUpper_of_integral_bounds
    (h : ∀ β : ℝ, 1 / 2 < β → β < 1 → ∃ C > (0 : ℝ),
      IntegralConvolutionBound β C ∧ IntegralShearBound β C) : UniformFourierUpper.{u,v} :=
  (uniformGridInputs_of_integral_bounds h).fourierUpper

end FiniteFourier
end LinearAlgebra
end OAI
