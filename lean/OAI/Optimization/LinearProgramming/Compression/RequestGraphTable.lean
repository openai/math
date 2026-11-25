import OAI.Optimization.LinearProgramming.Compression.RequestBasis
import OAI.Optimization.LinearProgramming.Lattice.BitSelectorConstants
import OAI.Optimization.LinearProgramming.Lattice.BitTables
import OAI.Computability.QuantumFactoring.BitStackRationalDivision

/-! Framed programs for the unit-coordinate graph matrix, its integer row
coefficients, and the affine slopes obtained from a selected row. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

abbrev ratVectorCode := Selector.vectorCode
def graphCode := listCode ratVectorCode
def rowArgCode := prodCode Nat.bits ratVectorCode

noncomputable def listCutoffP {α : Type} (e : α → List Bool) (d : α) :
    Procedure (listCode e) Nat.bits (fun xs => requestCutoff xs.length) := by
  let un := PriceGame.Control.Native.rowSizeP e d
  let pow := Selector.powTwoP.comp (unarySuccessor.comp (unarySuccessor.comp un))
  let plus := binaryAdd.comp ((listLength e d).pair (constant (listCode e) Nat.bits 3))
  exact binaryMul.comp (pow.pair plus)

def graphRow (w : List ℚ) (i : ℕ) : List ℚ :=
  (List.range w.length).map (fun j => if i=j then (1:ℚ) else 0) ++ [readAt 0 w i]

def graphRows (w : List ℚ) : List (List ℚ) := (List.range w.length).map (graphRow w)

noncomputable def graphRowP : Procedure rowArgCode ratVectorCode (fun x => graphRow x.2 x.1) := by
  let i := first Nat.bits ratVectorCode
  let w := second Nat.bits ratVectorCode
  let ctx := second Nat.bits rowArgCode
  let j := first Nat.bits rowArgCode
  let delta := conditional (natEqP (i.comp ctx) j) (constant _ ratCode (1:ℚ)) (constant _ ratCode 0)
  let cell : Procedure (prodCode Nat.bits rowArgCode) ratCode
      (fun x => if x.2.1=x.1 then (1:ℚ) else 0) := delta.congrFun (by intro x; simp)
  let units := tabulateBinaryAlongP (cell := fun (c : ℕ × List ℚ) j => if c.1=j then (1:ℚ) else 0)
    (0:ℚ) (0:ℚ) w cell
  let point := getAtP 0 w i
  let tail := (listCons ratCode).comp (point.pair (constant rowArgCode ratVectorCode []))
  exact (listAppend ratCode 0).comp (units.pair tail)

noncomputable def graphRowsP : Procedure ratVectorCode graphCode graphRows :=
  tabulateBinaryAlongP (cell := graphRow) (0:ℚ) ([]:List ℚ) (identity ratVectorCode) graphRowP

private theorem mapRange_ofFn {α : Type} {n : ℕ} (f : ℕ → α) (g : Fin n → α)
    (h : ∀ i : Fin n, f i.val=g i) : (List.range n).map f = List.ofFn g := by
  apply List.ext_getElem
  · simp
  · intro i _ hi
    have hn : i<n := by simpa using hi
    simpa using h ⟨i,hn⟩

theorem graphRow_pack {d : ℕ} (w : Fin d → ℚ) (i : Fin d) :
    graphRow (List.ofFn w) i.val = List.ofFn (requestInputRows w i) := by
  rw [List.ofFn_succ_last]
  simp only [requestInputRows_castSucc,requestInputRows_last,graphRow,List.length_ofFn,readAt_ofFn]
  congr 1
  exact mapRange_ofFn _ _ (fun j => by simp [Fin.ext_iff])

theorem graphRows_pack {d : ℕ} (w : Fin d → ℚ) :
    graphRows (List.ofFn w) = List.ofFn fun i => List.ofFn (requestInputRows w i) := by
  rw [graphRows,List.length_ofFn]
  exact mapRange_ofFn _ _ (graphRow_pack w)

def decodeRow (rows : List (List ℚ)) (i : ℕ) : List ℤ :=
  (List.range rows.length).map fun j => (readAt 0 (readAt [] rows i) j).num

noncomputable def decodeRowP : Procedure (prodCode Nat.bits graphCode) intRowCode
    (fun x => decodeRow x.2 x.1) := by
  let code := prodCode Nat.bits graphCode
  let ctx := second Nat.bits code
  let i := first Nat.bits graphCode
  let rows := second Nat.bits graphCode
  let row := getAtP ([]:List ℚ) rows i
  let q := getAtP (0:ℚ) (row.comp ctx) (first Nat.bits code)
  exact tabulateBinaryAlongP ([]:List ℚ) (0:ℤ) rows (ratNum.comp q)

theorem decodeRow_pack {d : ℕ} (A : Fin d → Fin (d+1) → ℚ) (i : Fin d) :
    decodeRow (List.ofFn fun t => List.ofFn (A t)) i.val = List.ofFn (requestDecodeRow (A i)) := by
  simp only [decodeRow,List.length_ofFn,readAt_ofFn]
  apply mapRange_ofFn
  intro j
  exact congrArg Rat.num (readAt_ofFn 0 (A i) j.castSucc)

def slopes (z : List ℤ) : List ℚ :=
  (List.range z.tail.length).map fun j =>
    -((readAt (α := ℤ) 0 z j : ℤ) : ℚ)/((readAt (α := ℤ) 0 z (z.length-1) : ℤ) : ℚ)

noncomputable def slopesP : Procedure intRowCode ratVectorCode slopes := by
  let ctx := second Nat.bits intRowCode
  let j := first Nat.bits intRowCode
  let top := ratNeg.comp (intToRat.comp (getAtP 0 ctx j))
  let last := (predIndexP (listLength intCode 0)).comp ctx
  let bot := intToRat.comp (getAtP 0 ctx last)
  exact tabulateBinaryAlongP (0:ℤ) (0:ℚ) (listTail intCode) (ratDiv.comp (top.pair bot))

theorem slopes_pack {n : ℕ} (z : Fin (n+1) → ℤ) :
    slopes (List.ofFn z) = List.ofFn (requestSlope z) := by
  simp only [slopes,List.length_tail,List.length_ofFn,Nat.add_sub_cancel]
  apply mapRange_ofFn
  intro j
  exact congrArg₂ (fun a b : ℤ => -(a:ℚ)/(b:ℚ))
    (readAt_ofFn 0 z j.castSucc) (readAt_ofFn 0 z (Fin.last n))

end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
