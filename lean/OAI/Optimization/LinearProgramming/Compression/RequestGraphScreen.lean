import OAI.Optimization.LinearProgramming.Compression.RequestGraphTable
import OAI.Optimization.LinearProgramming.Lattice.BitClearRows
import OAI.Optimization.LinearProgramming.PriceGame.ControlRatListSum
import OAI.Optimization.LinearProgramming.PriceGame.LearningGroupingIndex

/-! Screen the framed rational rows in input order. The binary procedure
returns the first qualifying index, or the actual row count on failure. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

def rowSquare (row : List ℚ) : ℚ := (row.map (fun q => q*q)).sum

def rowPass (d : ℕ) (row : List ℚ) : Bool :=
  decide ((readAt (0:ℚ) row (d-1)).num ≠ 0 ∧ rowSquare row ≤ (requestCutoff d : ℚ)^2)

def screenRows (rows : List (List ℚ)) : ℕ :=
  (rows.map (fun r => if rowPass rows.length r then (1:ℕ) else 0)).idxOf 1

noncomputable def cutoffP : Procedure graphCode Nat.bits (fun rs => requestCutoff rs.length) :=
  listCutoffP ratVectorCode []

noncomputable def rowSquareP : Procedure ratVectorCode ratCode rowSquare := by
  let sq := ratMul.comp ((identity ratCode).pair (identity ratCode))
  exact PriceGame.Control.Native.ratListSumP.comp (listMap (0:ℚ) (0:ℚ) sq)

noncomputable def rowPassP : Procedure (prodCode ratVectorCode graphCode) boolCode
    (fun x => rowPass x.2.length x.1) := by
  let row := first ratVectorCode graphCode
  let rows := second ratVectorCode graphCode
  let d := (listLength ratVectorCode []).comp rows
  let pivot := ratNum.comp (getAtP (0:ℚ) row (predIndexP d))
  let nz := boolNot.comp (binaryZero.comp (intAbs.comp pivot))
  let K := natToRat.comp (cutoffP.comp rows)
  let short := OracleSpec.Arithmetic.ratLe.comp ((rowSquareP.comp row).pair (ratMul.comp (K.pair K)))
  refine (boolAnd.comp (nz.pair short)).congrFun ?_
  rintro ⟨r,A⟩
  apply Bool.eq_iff_iff.mpr
  simp [rowPass,pow_two]

private theorem firstOrLength (ns : List ℕ) :
    let u := PriceGame.Learning.BitMachine.supportIndex (1,ns)
    (if u=0 then ns.length else u-1) = ns.idxOf 1 := by
  by_cases h : 1∈ns
  · simp [PriceGame.Learning.BitMachine.supportIndex,h]
  · simp [PriceGame.Learning.BitMachine.supportIndex,h]

noncomputable def screenRowsP : Procedure graphCode Nat.bits screenRows := by
  let bit := conditional rowPassP (constant _ Nat.bits 1) (constant _ Nat.bits 0)
  let flags := Selector.mapWithContextP (f := fun (A : List (List ℚ)) (r : List ℚ) =>
    if rowPass A.length r then (1:ℕ) else 0) ([]:List ℚ) (0:ℕ) (identity graphCode) bit
  let idx := PriceGame.Learning.BitMachine.supportIndexP.comp ((constant graphCode Nat.bits 1).pair flags)
  let result := conditional (binaryZero.comp idx) (listLength ratVectorCode []) (predIndexP idx)
  refine result.congrFun ?_
  intro A
  simpa only [Function.comp_apply,id_eq,screenRows,List.length_map,decide_eq_true_eq] using
    firstOrLength (A.map fun r => if rowPass A.length r then (1:ℕ) else 0)

end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
