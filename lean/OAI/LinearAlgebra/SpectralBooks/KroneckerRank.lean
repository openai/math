import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.RingTheory.Flat.Basic

/-! # Rank of a Kronecker product

In tensor product bases the image of a Kronecker product is the tensor
product of the images. Over a field, the natural inclusion of this tensor
product into the ambient space is injective.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Kronecker

/-- Matrix rank is multiplicative for Kronecker products over every field. -/
theorem rank_kronecker {K m n p q : Type*} [Field K]
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n K) (B : Matrix p q K) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  classical
  let bm := Pi.basisFun K m
  let bn := Pi.basisFun K n
  let bp := Pi.basisFun K p
  let bq := Pi.basisFun K q
  rw [(A ⊗ₖ B).rank_eq_finrank_range_toLin (bm.tensorProduct bp) (bn.tensorProduct bq),
    Matrix.toLin_kronecker, A.rank_eq_finrank_range_toLin bm bn,
    B.rank_eq_finrank_range_toLin bp bq, TensorProduct.range_map, ← TensorProduct.range_mapIncl,
    LinearMap.finrank_range_of_inj (Module.Flat.tensorProduct_mapIncl_injective_of_right _ _),
    Module.finrank_tensorProduct]

end SpectralBooks
end LinearAlgebra
end OAI
