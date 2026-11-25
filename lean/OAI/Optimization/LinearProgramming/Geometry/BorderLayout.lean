import OAI.Optimization.LinearProgramming.Compression.MinorBatchHeader
import OAI.Optimization.LinearProgramming.Geometry.Pivot

/-! Storage for one signed border-determinant batch in the geometric label oracle. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM Compression.MinorLoad Matrix

/-- Address-bank tables and scalar arrays occupy separate banks; the inequalities within
one bank put persistent data before the indicated scratch space. -/
structure Layout (r n : ℕ) where
  source : ℕ
  prices : ℕ
  triples : ℕ
  rounded : ℕ
  answers : ℕ
  scratch : ℕ
  pivots : ℕ
  headers : ℕ
  rows : ℕ
  cols : ℕ
  mask : ℕ
  source_ge : 256 ≤ source
  source_end : source+r*n ≤ prices
  prices_end : prices+n ≤ triples
  triples_end : triples+3*n ≤ rounded
  rounded_end : rounded+r*n ≤ answers
  answers_end : answers+n ≤ scratch
  pivots_ge : 256 ≤ pivots
  pivots_end : pivots+r ≤ headers
  headers_end : headers+6*n ≤ rows
  rows_end : rows+r ≤ cols
  cols_end : cols+n*(r+1) ≤ mask

namespace Layout

/-- One explicit choice of all addresses from the dimensions. -/
def standard (r n : ℕ) : Layout r n :=
  let source := 256
  let prices := source+r*n
  let triples := prices+n
  let rounded := triples+3*n
  let answers := rounded+r*n
  let scratch := answers+n
  let pivots := 256
  let headers := pivots+r
  let rows := headers+6*n
  let cols := rows+r
  let mask := cols+n*(r+1)
  ⟨source,prices,triples,rounded,answers,scratch,pivots,headers,rows,cols,mask,
    le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩

variable {K : Type} {r n k : ℕ}

/-- All column candidates for prefix `k+1`. The selected columns have their original pivot
order, and may end in a repeat, yielding precisely the signed (or zero) bordered minor. -/
def batch (L : Layout r n) (D : Matrix (Fin r) (Fin n) K) (hr : k+1 ≤ r) (J : Fin k → Fin n) :
    Compression.MinorLoad.BatchLayout K n where
  query j := {
    m := r, n := n, k := k+1, src := L.source, dst := L.scratch,
    rowArray := L.rows, colArray := L.cols + (k+1)*j.val, matrix := D,
    row := Fin.castLE hr, col := Fin.lastCases j J,
    src_pos := by have := L.source_ge; omega,
    disjoint := by have := L.source_end; have := L.prices_end; have := L.triples_end; have := L.rounded_end; have := L.answers_end; omega,
    rowArray_ge := by have := L.pivots_ge; have := L.pivots_end; have := L.headers_end; omega,
    colArray_ge := by have := L.pivots_ge; have := L.pivots_end; have := L.headers_end; have := L.rows_end; omega }
  headerBase := L.headers
  answerBase := L.answers
  header_ge := by have := L.pivots_ge; have := L.pivots_end; omega
  answer_ge := by have := L.source_ge; have := L.source_end; have := L.prices_end; have := L.triples_end; have := L.rounded_end; omega
  row_ge _ := by change 20 ≤ L.rows; have := L.pivots_ge; have := L.pivots_end; have := L.headers_end; omega
  col_ge j := by change 20 ≤ L.cols + (k+1)*j.val; have := L.pivots_ge; have := L.pivots_end; have := L.headers_end; have := L.rows_end; omega
  source_ge _ := by change 7 ≤ L.source; have := L.source_ge; omega
  source_end _ := by change L.source + r*n ≤ L.answers; have := L.source_end; have := L.prices_end; have := L.triples_end; have := L.rounded_end; omega
  answers_end _ := L.answers_end

/-- Persistent addresses and data available when a stage begins; no already-prepared
headers or per-candidate selectors are assumed. -/
structure Ready (L : Layout r n) (D : Matrix (Fin r) (Fin n) K) (J : Fin k → Fin n) (m : Memory K) : Prop where
  prefixCount : m.index 128 = k
  height : m.index 129 = r
  width : m.index 130 = n
  sourceAddr : m.index 131 = L.source
  priceAddr : m.index 132 = L.prices
  tripleAddr : m.index 133 = L.triples
  roundedAddr : m.index 134 = L.rounded
  pivotAddr : m.index 136 = L.pivots
  headerAddr : m.index 140 = L.headers
  rowAddr : m.index 141 = L.rows
  colAddr : m.index 142 = L.cols
  answerAddr : m.index 143 = L.answers
  scratchAddr : m.index 144 = L.scratch
  maskAddr : m.index 145 = L.mask
  pivotData (q : Fin k) : m.index (L.pivots+q.val) = (J q).val
  matrixData (i : Fin r) (j : Fin n) : m.data (L.source + i.val*n+j.val) = D i j

end Layout
end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
