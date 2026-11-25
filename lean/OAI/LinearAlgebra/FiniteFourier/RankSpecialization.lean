import OAI.NumberTheory.SiegelZeros.Hilbert.HomogeneousDeformation

/-! # Rank of a rational matrix at regular evaluation points -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

noncomputable section

variable {K μ ι : Type*} [Field K]

/-- A rational matrix written with one common denominator. -/
def rationalQuotient (P : Matrix μ ι K[X]) (h : K[X]) : Matrix μ ι (RatFunc K) :=
  fun i j ↦ algebraMap K[X] (RatFunc K) (P i j) / algebraMap K[X] (RatFunc K) h

/-- Specialization of the common-denominator presentation at `t`. -/
def quotientAt (P : Matrix μ ι K[X]) (h : K[X]) (t : K) : Matrix μ ι K :=
  fun i j ↦ (P i j).eval t / h.eval t

/-- A nonvanishing denominator scales all entries by one unit. The rank bound then follows
from specialization of the polynomial numerator matrix by nonvanishing minors. -/
theorem rank_quotientAt_le [Fintype μ] [Fintype ι]
    (P : Matrix μ ι K[X]) (h : K[X]) (t : K) (ht : h.eval t ≠ 0) :
    (quotientAt P h t).rank ≤ (rationalQuotient P h).rank := by
  have hn : h ≠ 0 := fun e ↦ ht (by simp [e])
  have hK : algebraMap K[X] (RatFunc K) h ≠ 0 := by
    simpa using (RatFunc.algebraMap_injective K).ne hn
  have he : quotientAt P h t = (h.eval t)⁻¹ • P.map (evalRingHom t) := by
    ext i j
    simp [quotientAt, div_eq_inv_mul]
  have hq : rationalQuotient P h = (algebraMap K[X] (RatFunc K) h)⁻¹ •
      P.map (algebraMap K[X] (RatFunc K)) := by
    ext i j
    simp [rationalQuotient, div_eq_inv_mul]
  rw [he, hq, Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero ht)),
    Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero hK))]
  exact SiegelZeros.WeightedTorusJets.Geometry.rank_polynomial_eval_le P t

end

end FiniteFourier
end LinearAlgebra
end OAI
