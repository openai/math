import OAI.Optimization.LinearProgramming.Geometry.LabelBuffers

/-! Retained register headers and row-major values of a marked subspace's two
complementary matrices, shared by the input initializer and every price request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PriceLayout

open RAM Geometry
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r s n : ℕ}

structure Matrices (x : LabelInput.Buffers r s n) (D : Matrix (Fin r) (Fin n) K)
    (E : Matrix (Fin s) (Fin n) K) (m : Memory K) : Prop where
  rank : m.index 129=r
  columns : m.index 130=n
  primalBase : m.index 131=x.primal
  priceBase : m.index 132=x.price
  freeBase : m.index 133=x.free
  indexBase : m.index 136=x.indices
  dualBase : m.index 147=x.dual
  dualRank : m.index 148=s
  primal (i : Fin r) (j : Fin n) : m.data (x.primal+i.val*n+j.val)=D i j
  dual (i : Fin s) (j : Fin n) : m.data (x.dual+i.val*n+j.val)=E i j

end PriceLayout
end Recovery
end LinearProgramming
end Optimization
end OAI
