import OAI.LinearAlgebra.FiniteFourier.OpenConvolution
import OAI.LinearAlgebra.FiniteFourier.FixedConvolution

/-! # Polynomial and vector forms of open convolution -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- Evaluating the formal convolution coefficient on the two operands gives
the corresponding output of ordinary untruncated convolution. -/
theorem eval_convolutionCoefficient_openConv (R : Type*) [CommRing R] (n : ℕ)
    (x y : Fin n → R) (k : Fin (2*n-1)) :
    MvPolynomial.eval (Sum.elim x y) (convolutionCoefficient R n k.val) =
      openConv R n x y k := by
  simp [convolutionCoefficient, openConv, Finset.mul_sum, apply_ite]

end FiniteFourier
end LinearAlgebra
end OAI
