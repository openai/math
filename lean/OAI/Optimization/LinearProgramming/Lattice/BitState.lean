import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Optimization.LinearProgramming.Lattice.BitBasicCodes
import HexLLL.Native
import Mathlib.Data.List.OfFn

/-! A single row-major encoding serves every dimension of the integral LLL reducer.
Indices are binary. The list frames expose the actual row and column counts.
The state being encoded is from Kim Morrison's [Hex LLL implementation](https://github.com/leanprover/hex-lll/blob/5676b60afa8401aea99c77091e94152d07e9c222/HexLLL/Native.lean)
(© 2026 Lean FRO, LLC, Apache-2.0). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

abbrev State := IntMatrix × (IntMatrix × List ℕ)
abbrev ColumnArg := (ℕ × ℕ) × State
abbrev Cursor := ℕ × State

def gramListCode := listCode Nat.bits
def stateCode := prodCode intMatrixCode (prodCode intMatrixCode gramListCode)
def columnArgCode := prodCode (prodCode Nat.bits Nat.bits) stateCode
def cursorCode := prodCode Nat.bits stateCode

def packVector {α : Type} {n : ℕ} (v : Vector α n) : List α :=
  List.ofFn (fun i => v.get i)

def packMatrix {n m : ℕ} (A : Hex.Matrix ℤ n m) : IntMatrix :=
  List.ofFn fun i => packVector (A.getRow i)

def packState {n m : ℕ} (s : Hex.Internal.LLLState n m) : State :=
  (packMatrix s.b, packMatrix s.ν, packVector s.d)

def readAt {α : Type} (d : α) (xs : List α) (i : ℕ) : α := (xs.drop i).headD d

def rowAt (A : IntMatrix) (i : ℕ) : List ℤ := readAt [] A i
def entryAt (A : IntMatrix) (i j : ℕ) : ℤ := readAt 0 (rowAt A i) j

@[simp] theorem length_packVector {α : Type} {n : ℕ} (v : Vector α n) :
    (packVector v).length = n := by simp [packVector]

@[simp] theorem length_packMatrix {n m : ℕ} (A : Hex.Matrix ℤ n m) :
    (packMatrix A).length = n := by simp [packMatrix]

@[simp] theorem readAt_ofFn {α : Type} {n : ℕ} (d : α) (f : Fin n → α) (i : Fin n) :
    readAt d (List.ofFn f) i.val = f i := by
  simp [readAt, i.isLt]

@[simp] theorem readAt_packVector {α : Type} {n : ℕ} (d : α) (v : Vector α n) (i : Fin n) :
    readAt d (packVector v) i.val = v.get i := readAt_ofFn d _ i

@[simp] theorem rowAt_packMatrix {n m : ℕ} (A : Hex.Matrix ℤ n m) (i : Fin n) :
    rowAt (packMatrix A) i.val = packVector (A.getRow i) := readAt_ofFn [] _ i

@[simp] theorem entryAt_packMatrix {n m : ℕ} (A : Hex.Matrix ℤ n m) (i : Fin n) (j : Fin m) :
    entryAt (packMatrix A) i.val j.val = (A.getRow i).get j := by
  simp [entryAt]

noncomputable def basisP : Procedure stateCode intMatrixCode (fun s : State => s.1) :=
  first intMatrixCode (prodCode intMatrixCode gramListCode)

noncomputable def nuMatrixP : Procedure stateCode intMatrixCode (fun s : State => s.2.1) :=
  (first intMatrixCode gramListCode).comp (second intMatrixCode (prodCode intMatrixCode gramListCode))

noncomputable def gramsP : Procedure stateCode gramListCode (fun s : State => s.2.2) :=
  (second intMatrixCode gramListCode).comp (second intMatrixCode (prodCode intMatrixCode gramListCode))

noncomputable def matrixEntryP : Procedure (prodCode (prodCode Nat.bits Nat.bits) intMatrixCode)
    intCode (fun x => entryAt x.2 x.1.1 x.1.2) := by
  let ij := first (prodCode Nat.bits Nat.bits) intMatrixCode
  let i := (first Nat.bits Nat.bits).comp ij
  let j := (second Nat.bits Nat.bits).comp ij
  let rows := second (prodCode Nat.bits Nat.bits) intMatrixCode
  let row := (listGet intRowCode []).comp (i.pair rows)
  exact (listGet intCode 0).comp (j.pair row)

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
