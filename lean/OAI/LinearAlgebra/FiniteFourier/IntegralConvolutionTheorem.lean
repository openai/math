import OAI.LinearAlgebra.FiniteFourier.AtTwoPackedReduction
import OAI.LinearAlgebra.FiniteFourier.DyadicPackedCircuits
import OAI.LinearAlgebra.FiniteFourier.IntegralTensorBound

/-! # Division-free convolution for the finite abelian Fourier upper bound

The three protected reductions and the prime tensor kernels give the total
gate estimate for integer polynomial multiplication used in Theorem 1.1.
The exponent has two strict intermediates to absorb the width overhead and
the polylogarithmic cost of the shorter products.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- The Gaussian dyadic circuits and the ternary circuit at two have
uniform budgets for every exponent above one half. -/
theorem protectedConvolutionCircuits {β : ℝ} (hβ : 1/2 < β) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      AtTwoPackedCircuits β C₀ ∧ DyadicPackedCircuits GaussianRationals β C₁ := by
  have hβ' : 0 ≤ β := by linarith
  obtain ⟨C, hC, ht⟩ := integralShearBound hβ
  obtain ⟨C₀, h₀, ha⟩ := atTwoPackedCircuits_of_integralShear hβ' hC.le ht
  obtain ⟨C₁, h₁, hd⟩ := dyadicPackedCircuits_of_integralShear hβ' hC.le ht
  exact ⟨C₀, C₁, h₀, h₁, ha, hd⟩

/-- For every exponent above one half there are formal integer polynomial
multiplication circuits with total cost at most `C n (1 + log₂ n)^α`, for one
constant over all input lengths. -/
theorem integralConvolutionBound {α : ℝ} (hα : 1/2 < α) :
    ∃ C > (0 : ℝ), IntegralConvolutionBound α C := by
  obtain ⟨γ, hγ, hγ'⟩ := exists_between (lt_min hα (by norm_num : (1/2:ℝ) < 1))
  obtain ⟨β, hβ, hβγ⟩ := exists_between hγ
  obtain ⟨C₀, C₁, h₀, h₁, ha, hd⟩ := protectedConvolutionCircuits hβ
  have hγ₁ := (lt_min_iff.mp hγ').2.le
  have hs := integralOpenDescent_of_packedCircuits (by linarith : 0 ≤ β) hβγ hγ₁ h₀.le h₁.le ha hd
  exact hs.integralConvolutionBound (by linarith) hγ₁ (lt_min_iff.mp hγ').1

end FiniteFourier
end LinearAlgebra
end OAI
