import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Pi
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

variable {K : Type*}

open Matrix

variable {I J K : Type*} [Fintype I] [Fintype J]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A feasible dual multiplier bounds the objective at every feasible primal point. -/
theorem weak_duality {A : Matrix I J K} {b y : I → K} {c x : J → K}
    (hx : A *ᵥ x ≤ b) (hy : 0 ≤ y) (hdual : Aᵀ *ᵥ y = c) : c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  calc
    c ⬝ᵥ x = y ⬝ᵥ (A *ᵥ x) := by rw [← hdual, mulVec_transpose, dotProduct_mulVec]
    _ ≤ y ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hx hy
    _ = b ⬝ᵥ y := dotProduct_comm _ _

/-- At a feasible base point the joint certificate forces a strictly negative normalization denominator. -/
theorem negative_ray_denominator {A : Matrix I J K} {x₀ f c : J → K} {l μ b : I → K} {θ : K}
    (hfeas : A *ᵥ x₀ ≤ b) (hl : 0 ≤ l) (hμ : 0 ≤ μ) (hθ : 0 ≤ θ)
    (hdual : Aᵀ *ᵥ l = θ • c) (hprimal : A *ᵥ f + θ • b = μ)
    (hneg : b ⬝ᵥ l + c ⬝ᵥ f < 0) :
    A *ᵥ f = μ ∧ c ⬝ᵥ f < 0 := by
  have hprod : l ⬝ᵥ μ = θ * (b ⬝ᵥ l + c ⬝ᵥ f) := by
    rw [← hprimal, dotProduct_add, dotProduct_mulVec, ← mulVec_transpose, hdual,
      smul_dotProduct, dotProduct_smul, dotProduct_comm l b, smul_eq_mul, smul_eq_mul]
    ring
  have hzero : θ = 0 := by
    by_contra! hn
    have hlt := mul_neg_of_pos_of_neg (lt_of_le_of_ne hθ (Ne.symm hn)) hneg
    exact (not_lt_of_ge (dotProduct_nonneg_of_nonneg hl hμ)) (hprod.trans_lt hlt)
  subst θ
  simp only [zero_smul, add_zero] at hdual hprimal
  have hlb : 0 ≤ b ⬝ᵥ l := by simpa only [zero_dotProduct] using weak_duality hfeas hl hdual
  have hcf : c ⬝ᵥ f < 0 := by linarith
  exact ⟨hprimal,hcf⟩

/-- The certificate for the joint primal–dual instance yields a direction with unit gain. -/
theorem ray_of_multipliers {A : Matrix I J K} {x₀ f c : J → K} {l μ b : I → K} {θ : K}
    (hfeas : A *ᵥ x₀ ≤ b) (hl : 0 ≤ l) (hμ : 0 ≤ μ) (hθ : 0 ≤ θ)
    (hdual : Aᵀ *ᵥ l = θ • c) (hprimal : A *ᵥ f + θ • b = μ)
    (hneg : b ⬝ᵥ l + c ⬝ᵥ f < 0) :
    A *ᵥ ((c ⬝ᵥ f)⁻¹ • f) ≤ 0 ∧ c ⬝ᵥ ((c ⬝ᵥ f)⁻¹ • f) = 1 := by
  obtain ⟨hprimal,hcf⟩ := negative_ray_denominator hfeas hl hμ hθ hdual hprimal hneg
  constructor
  · rw [mulVec_smul, hprimal]
    intro i
    exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hcf.le) (hμ i)
  · rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hcf.ne]

end PrimalDual
end LinearProgramming
end Optimization
end OAI
