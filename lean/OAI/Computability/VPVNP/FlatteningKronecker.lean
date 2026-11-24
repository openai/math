import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Basic

/-!
# Rank of a product flattening

The Kronecker product acts as the tensor product of the associated linear maps.
Its range identifies with the tensor product of the two ranges.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

/-- Ranks multiply under Kronecker products of rectangular matrices over any field. -/
theorem rank_kronecker {k m n i j : Type*} [Field k]
    [Fintype m] [Fintype n] [Fintype i] [Fintype j] (A : Matrix m n k) (B : Matrix i j k) :
    (Matrix.kronecker A B).rank = A.rank * B.rank := by
  classical
  let bm := Pi.basisFun k m
  let bn := Pi.basisFun k n
  let bi := Pi.basisFun k i
  let bj := Pi.basisFun k j
  rw [Matrix.rank_eq_finrank_range_toLin _ (bm.tensorProduct bi) (bn.tensorProduct bj),
    Matrix.kronecker, Matrix.toLin_kronecker, Matrix.rank_eq_finrank_range_toLin A bm bn,
    Matrix.rank_eq_finrank_range_toLin B bi bj, TensorProduct.range_map,
    ← TensorProduct.range_mapIncl, LinearMap.finrank_range_of_inj, Module.finrank_tensorProduct]
  exact Module.Flat.tensorProduct_mapIncl_injective_of_right _ _

end WireTensor

end VPVNP
end Computability
end OAI
