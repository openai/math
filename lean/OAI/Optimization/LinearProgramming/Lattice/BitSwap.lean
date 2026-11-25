import OAI.Optimization.LinearProgramming.Lattice.BitGramRead
import OAI.Optimization.LinearProgramming.Lattice.BitMatrix

/-! A fixed framed bit-stack implementation of the adjacent integral LLL swap.
Each trailing coefficient pair is computed from the same input matrix. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

def swapNuEntry (k : ℕ) (s : State) (i j : ℕ) : ℤ :=
  let p := k-1
  let A := s.2.1
  let old := entryAt A i j
  if i=p then
    if j<p then entryAt A k j else old
  else if i=k then
    if j<p then entryAt A p j else old
  else if k < i then
    let pair := swapPair (gramQuad k s,(entryAt A i k,entryAt A i p))
    if j=p then pair.1 else if j=k then pair.2 else old
  else old

def swapNuRow (k : ℕ) (s : State) (i : ℕ) : List ℤ :=
  (List.range (rowAt s.2.1 i).length).map (swapNuEntry k s i)

def swapStep (k : ℕ) (s : State) : State :=
  if 0 < k ∧ k < s.1.length then
    (swapRows (k-1) k s.1, (List.range s.2.1.length).map (swapNuRow k s),
      s.2.2.set k (swappedGram (gramQuad k s)))
  else s

def swapRowArgCode := prodCode Nat.bits cursorCode
def swapCellArgCode := prodCode Nat.bits swapRowArgCode

noncomputable def swapNuEntryP : Procedure swapCellArgCode intCode
    (fun x => swapNuEntry x.2.2.1 x.2.2.2 x.2.1 x.1) := by
  let j := first Nat.bits swapRowArgCode
  let row := second Nat.bits swapRowArgCode
  let i := (first Nat.bits cursorCode).comp row
  let cursor := (second Nat.bits cursorCode).comp row
  let k := (first Nat.bits stateCode).comp cursor
  let p := predIndexP k
  let s := (second Nat.bits stateCode).comp cursor
  let A := nuMatrixP.comp s
  let old := tableEntryP A i j
  let g := gramQuadP.comp cursor
  let operands := (tableEntryP A i k).pair (tableEntryP A i p)
  let q := swapPairP.comp (g.pair operands)
  let trailing := conditional (natEqP j p) ((first intCode intCode).comp q)
    (conditional (natEqP j k) ((second intCode intCode).comp q) old)
  let below := binaryLt.comp (j.pair p)
  let left := conditional below (tableEntryP A k j) old
  let right := conditional below (tableEntryP A p j) old
  exact (conditional (natEqP i p) left (conditional (natEqP i k) right
    (conditional (binaryLt.comp (k.pair i)) trailing old))).congrFun (by intro x; simp [swapNuEntry])

noncomputable def swapNuRowP : Procedure swapRowArgCode intRowCode
    (fun x => swapNuRow x.2.1 x.2.2 x.1) := by
  let i := first Nat.bits cursorCode
  let cursor := second Nat.bits cursorCode
  let s := (second Nat.bits stateCode).comp cursor
  exact tabulateBinaryAlongP 0 0 (tableRowP (nuMatrixP.comp s) i) swapNuEntryP

noncomputable def swapStepP : Procedure cursorCode stateCode (fun x : Cursor => swapStep x.1 x.2) := by
  let k := first Nat.bits stateCode
  let p := predIndexP k
  let s := second Nat.bits stateCode
  let b := basisP.comp s
  let n := (listLength intRowCode []).comp b
  let valid := boolAnd.comp ((binaryLt.comp ((constant cursorCode Nat.bits 0).pair k)).pair
    (binaryLt.comp (k.pair n)))
  let swapped := swapRowsP.comp ((p.pair k).pair b)
  let nu := tabulateBinaryAlongP (ea := intRowCode) (ed := intRowCode)
    (cell := fun c : Cursor => swapNuRow c.1 c.2) [] [] (nuMatrixP.comp s) swapNuRowP
  let g := swappedGramP.comp gramQuadP
  let ds := (setNthP Nat.bits 0).comp ((k.pair g).pair (gramsP.comp s))
  exact (conditional valid (swapped.pair (nu.pair ds)) s).congrFun (by
    rintro ⟨k,s⟩
    change (if decide (0<k) && decide (k<s.1.length) then _ else _) = _
    by_cases hp : 0<k <;> by_cases hn : k<s.1.length <;> simp [swapStep,hp,hn])

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
