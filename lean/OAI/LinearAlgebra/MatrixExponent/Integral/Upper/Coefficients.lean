import OAI.LinearAlgebra.MatrixExponent.Integral.Interpolation
import OAI.LinearAlgebra.TensorSpectrum.Additive.RankAnalysis
import OAI.LinearAlgebra.MatrixExponent.LocalTensor
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper
open OAI.MatrixMultiplication.Foundation

def matrixTensor (a b c : ℕ) :
    Tensor O (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  Tensor.matrixCoefficients (Fin a) (Fin b) (Fin c)

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper
