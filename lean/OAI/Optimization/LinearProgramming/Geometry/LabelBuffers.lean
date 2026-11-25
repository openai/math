import OAI.Optimization.LinearProgramming.Geometry.BorderLayout
import OAI.Optimization.LinearProgramming.Geometry.LabelBasis

/-! Relocatable input and output locations for the geometric Boolean label. The dual matrix,
primal matrix and scalar price vector may belong to arbitrary retained caller storage. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelInput

open RAM BorderBatch Matrix

structure Buffers (r s n : ℕ) where
  dual : ℕ
  primal : ℕ
  price : ℕ
  free : ℕ
  indices : ℕ
  dualHigh : 256 ≤ dual
  dualEnd : dual+s*n ≤ primal
  primalEnd : primal+r*n ≤ price
  priceEnd : price+n ≤ free
  indicesHigh : 256 ≤ indices

/-- The matrix and prices stay in the caller's tapes; new scalar arrays begin at `free`.
The address-bank work arrays begin at `indices`, independently of the scalar addresses. -/
def Buffers.layout {r s n : ℕ} (x : Buffers r s n) : BorderBatch.Layout r n :=
  let rounded := x.free+3*n
  let answers := rounded+r*n
  let headers := x.indices+r
  let rows := headers+6*n
  let cols := rows+r
  ⟨x.primal,x.price,x.free,rounded,answers,answers+n,x.indices,headers,rows,cols,cols+n*(r+1),
    by have := x.dualHigh; have := x.dualEnd; omega,x.primalEnd,x.priceEnd,le_rfl,le_rfl,le_rfl,
    x.indicesHigh,le_rfl,le_rfl,le_rfl,le_rfl⟩

variable {K : Type} {r s n : ℕ}

/-- Input ABI for the relocatable label call. An entry in the price tape is a scalar in `K`,
with one entry per coordinate. The two matrix tapes are independently row major. -/
structure Inputs (x : Buffers r s n) (D : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K)
    (price : Fin n → K) (i : Fin n) (m : Memory K) : Prop where
  dualAddr : m.index 200=x.dual
  indexAddr : m.index 201=x.indices
  rank : m.index 202=r
  dualRank : m.index 203=s
  columns : m.index 204=n
  index : m.index 205=i.val
  primalAddr : m.index 206=x.primal
  priceAddr : m.index 207=x.price
  freeAddr : m.index 208=x.free
  primal (a : Fin r) (b : Fin n) : m.data (x.primal+a.val*n+b.val)=D a b
  dual (a : Fin s) (b : Fin n) : m.data (x.dual+a.val*n+b.val)=E a b
  prices (b : Fin n) : m.data (x.price+b.val)=price b

/-- Fields consumed by the signed-minor batch, prefix walker and post-prefix projection. -/
structure Header (x : Buffers r s n) (D : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K)
    (price : Fin n → K) (i : Fin n) (m : Memory K) : Prop where
  batch : x.layout.Ready D (Fin.elim0 : Fin 0 → Fin n) m
  rowCursor : m.index 135=x.layout.rounded
  pivotCursor : m.index 137=x.indices
  precision : m.index 138=geoCutoff n
  accepted : m.index 139=0
  index : m.index 146=i.val
  dualAddr : m.index 147=x.dual
  dualRank : m.index 148=s
  afterPivotFree : m.index 149=x.layout.scratch
  dual (a : Fin s) (b : Fin n) : m.data (x.dual+a.val*n+b.val)=E a b
  prices (b : Fin n) : m.data (x.price+b.val)=price b

end LabelInput
end Geometry
end LinearProgramming
end Optimization
end OAI
