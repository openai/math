import OAI.Optimization.LinearProgramming.Compression.RequestGraphScreen
import OAI.Optimization.LinearProgramming.Compression.RequestNative
import OAI.Optimization.LinearProgramming.Lattice.BitRationalNative

/-! Build the graph of the rounded vector, physically reduce the entire rational
table, and retain the first eligible integer vector. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

abbrev Input := ℕ × List ℚ
def inputCode := prodCode Nat.bits ratVectorCode

noncomputable def reducedGraphRows (w : List ℚ) := lllRatRows (graphRows w)

noncomputable def reducedGraphRowsP : Procedure ratVectorCode graphCode reducedGraphRows :=
  lllRatRowsP.comp graphRowsP

theorem reducedGraphRows_pack {n : ℕ} (w : Fin (n+1) → ℚ) :
    reducedGraphRows (List.ofFn w) = Selector.packedTable (nativeGraphRowReducer n w) := by
  unfold reducedGraphRows
  rw [graphRows_pack]
  exact lllRatRows_pack (requestInputRows w) (requestRealRow_input_independent w)

noncomputable def prepare (x : Input) : Bool × (ℕ × List ℤ) :=
  let rows := reducedGraphRows x.2
  let i := screenRows rows
  (decide (i<rows.length),x.1,decodeRow rows i)

noncomputable def prepareP : Procedure inputCode (prodCode boolCode (prodCode Nat.bits intRowCode)) prepare := by
  let w := second Nat.bits ratVectorCode
  let q := first Nat.bits ratVectorCode
  let rows := reducedGraphRowsP.comp w
  let idx := screenRowsP.comp rows
  let z := decodeRowP.comp (idx.pair rows)
  let accepted := binaryLt.comp (idx.pair ((listLength ratVectorCode []).comp rows))
  exact accepted.pair (q.pair z)

theorem prepare_pack_row {n : ℕ} (q : ℕ) (w : Fin (n+1) → ℚ) (i : Fin (n+1))
    (h : screenRows (Selector.packedTable (nativeGraphRowReducer n w))=i.val) :
    prepare (q,List.ofFn w) =
      (true,q,List.ofFn (requestDecodeRow (nativeGraphRowReducer n w i))) := by
  simp only [prepare,reducedGraphRows_pack,h]
  simp only [Selector.packedTable,List.length_ofFn,decodeRow_pack,decide_eq_true i.isLt]

theorem prepare_pack_miss {n : ℕ} (q : ℕ) (w : Fin (n+1) → ℚ)
    (h : screenRows (Selector.packedTable (nativeGraphRowReducer n w))=n+1) :
    (prepare (q,List.ofFn w)).1=false := by
  change decide (screenRows (reducedGraphRows (List.ofFn w)) <
    (reducedGraphRows (List.ofFn w)).length) = false
  rw [reducedGraphRows_pack,h]
  exact decide_eq_false (by
    simpa only [Selector.packedTable,List.length_ofFn] using Nat.lt_irrefl (n+1))

end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
