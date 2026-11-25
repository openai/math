import OAI.Optimization.LinearProgramming.Lattice.BitTables
import OAI.Optimization.LinearProgramming.Lattice.BitArithmetic

/-! Entry formulas for one reduction column of the stored integral LLL state. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

def columnPair (x : ColumnArg) : ℤ × ℕ :=
  (entryAt x.2.2.1 x.1.2 x.1.1, readAt 0 x.2.2.2 (x.1.1+1))

def columnBasisEntry (x : ColumnArg) (i : ℕ) : ℤ :=
  entryAt x.2.1 x.1.2 i - nearest (columnPair x) * entryAt x.2.1 x.1.1 i

def columnNuEntry (x : ColumnArg) (i : ℕ) : ℤ :=
  let j := x.1.1
  let y := entryAt x.2.2.1 x.1.2 i
  let r := nearest (columnPair x)
  if i < j then y - r*entryAt x.2.2.1 j i else
    if i = j then y-r*(columnPair x).2 else y

def columnBasisRow (x : ColumnArg) : List ℤ :=
  (List.range (rowAt x.2.1 x.1.2).length).map (columnBasisEntry x)

def columnNuRow (x : ColumnArg) : List ℤ :=
  (List.range (rowAt x.2.2.1 x.1.2).length).map (columnNuEntry x)

def sizeReduceColumn (j k : ℕ) (s : State) : State :=
  let x : ColumnArg := ((j,k),s)
  if needsReduction (columnPair x) then
    (s.1.set k (columnBasisRow x), s.2.1.set k (columnNuRow x), s.2.2)
  else s

noncomputable def colJP : Procedure columnArgCode Nat.bits (fun x : ColumnArg => x.1.1) :=
  (first Nat.bits Nat.bits).comp (first (prodCode Nat.bits Nat.bits) stateCode)

noncomputable def colKP : Procedure columnArgCode Nat.bits (fun x : ColumnArg => x.1.2) :=
  (second Nat.bits Nat.bits).comp (first (prodCode Nat.bits Nat.bits) stateCode)

noncomputable def colStateP : Procedure columnArgCode stateCode (fun x : ColumnArg => x.2) :=
  second (prodCode Nat.bits Nat.bits) stateCode

noncomputable def columnPairP : Procedure columnArgCode (prodCode intCode Nat.bits) columnPair :=
  (tableEntryP (nuMatrixP.comp colStateP) colKP colJP).pair
    (getAtP 0 (gramsP.comp colStateP) (succIndexP colJP))

noncomputable def columnBasisEntryP : Procedure (prodCode Nat.bits columnArgCode) intCode
    (fun x => columnBasisEntry x.2 x.1) := by
  let i := first Nat.bits columnArgCode
  let x := second Nat.bits columnArgCode
  let A := basisP.comp (colStateP.comp x)
  let r := nearestP.comp (columnPairP.comp x)
  let a := tableEntryP A (colKP.comp x) i
  let b := tableEntryP A (colJP.comp x) i
  exact subMulP.comp (a.pair (r.pair b))

noncomputable def columnNuEntryP : Procedure (prodCode Nat.bits columnArgCode) intCode
    (fun x => columnNuEntry x.2 x.1) := by
  let i := first Nat.bits columnArgCode
  let x := second Nat.bits columnArgCode
  let A := nuMatrixP.comp (colStateP.comp x)
  let j := colJP.comp x
  let p := columnPairP.comp x
  let r := nearestP.comp p
  let a := tableEntryP A (colKP.comp x) i
  let b := tableEntryP A j i
  let d := natToInt.comp ((second intCode Nat.bits).comp p)
  let update := subMulP.comp (a.pair (r.pair b))
  let pivot := subMulP.comp (a.pair (r.pair d))
  exact (conditional (binaryLt.comp (i.pair j)) update
    (conditional (natEqP i j) pivot a)).congrFun (by intro x; simp [columnNuEntry, subMul])

noncomputable def columnBasisRowP : Procedure columnArgCode intRowCode columnBasisRow :=
  tabulateBinaryAlongP 0 0 (tableRowP (basisP.comp colStateP) colKP) columnBasisEntryP

noncomputable def columnNuRowP : Procedure columnArgCode intRowCode columnNuRow :=
  tabulateBinaryAlongP 0 0 (tableRowP (nuMatrixP.comp colStateP) colKP) columnNuEntryP

/-- The entire single-column transition, with binary indexing, signed updates,
and conditional row replacement implemented by one finite bit program. -/
noncomputable def sizeReduceColumnP : Procedure columnArgCode stateCode
    (fun x : ColumnArg => sizeReduceColumn x.1.1 x.1.2 x.2) := by
  let setRow := setNthP intRowCode []
  let b := setRow.comp ((colKP.pair columnBasisRowP).pair (basisP.comp colStateP))
  let v := setRow.comp ((colKP.pair columnNuRowP).pair (nuMatrixP.comp colStateP))
  let d := gramsP.comp colStateP
  exact conditional (needsReductionP.comp columnPairP) (b.pair (v.pair d)) colStateP

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
