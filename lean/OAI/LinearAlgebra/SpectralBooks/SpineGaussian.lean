import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The standard Gaussian on a page of the book

The component on the spine and the normal coordinate are independent,
with the standard Gaussian laws on their respective spaces.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory WithLp

section

/-- Appending an independent real standard normal to a standard Gaussian
on the spine gives the standard Gaussian on a page. -/
theorem stdGaussian_prod_gaussianReal_map (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ((stdGaussian E).prod (gaussianReal 0 1)).map (toLp 2) = stdGaussian (WithLp 2 (E × ℝ)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_prod, charFun_stdGaussian, charFun_stdGaussian, charFun_gaussianReal,
    ← Complex.exp_add]
  congr 1
  simp only [← Complex.ofReal_pow, WithLp.prod_norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]
  ring

end

end SpectralBooks
end LinearAlgebra
end OAI
