import OAI.Optimization.LinearProgramming.Lattice.BitSelectorPre
import OAI.Optimization.LinearProgramming.Lattice.LLLReduction

/-! Decode the first reduced integral row on the same bit machine as the LLL procedure. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Selector
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

def rowCoordinate (x : Frame) (i : ℕ) : ℚ := (entryAt x.2 0 i : ℚ) / (x.1.2.2 : ℚ)
def recoveredQ (x : Frame) : ℤ := (rowCoordinate x 0 / x.1.2.1).num
def recoveredZ (x : Frame) (i : ℕ) : ℤ :=
  let q := recoveredQ x
  let z := ((q:ℚ)*readAt 0 x.1.1 i-rowCoordinate x (i+1)).num
  if 0 ≤ q then z else -z

def finish (x : Frame) : ℕ × List ℤ :=
  ((recoveredQ x).natAbs,(List.range x.1.1.length).map (recoveredZ x))

noncomputable def contextFieldP : Procedure frameCode contextCode (fun x : Frame => x.1) :=
  first contextCode intMatrixCode

noncomputable def coordinatesP : Procedure frameCode vectorCode (fun x : Frame => x.1.1) :=
  (first vectorCode (prodCode ratCode Nat.bits)).comp contextFieldP

noncomputable def constantsP : Procedure frameCode (prodCode ratCode Nat.bits) (fun x : Frame => x.1.2) :=
  (second vectorCode (prodCode ratCode Nat.bits)).comp contextFieldP

noncomputable def rowCoordinateP {A : Type} {ea : A → List Bool} {x : A → Frame} {i : A → ℕ}
    (frame : Procedure ea frameCode x) (index : Procedure ea Nat.bits i) :
    Procedure ea ratCode (fun a => rowCoordinate (x a) (i a)) := by
  let A := (second contextCode intMatrixCode).comp frame
  let val := intToRat.comp (tableEntryP A (constant ea Nat.bits 0) index)
  let scale := natToRat.comp ((second ratCode Nat.bits).comp (constantsP.comp frame))
  exact ratDiv.comp (val.pair scale)

noncomputable def recoveredQP : Procedure frameCode intCode recoveredQ := by
  let v := rowCoordinateP (identity frameCode) (constant frameCode Nat.bits 0)
  let alpha := (first ratCode Nat.bits).comp constantsP
  exact ratNum.comp (ratDiv.comp (v.pair alpha))

noncomputable def recoveredZP : Procedure (prodCode Nat.bits frameCode) intCode
    (fun x => recoveredZ x.2 x.1) := by
  let code := prodCode Nat.bits frameCode
  let f := second Nat.bits frameCode
  let i := first Nat.bits frameCode
  let q := recoveredQP.comp f
  let u := getAtP (0:ℚ) (coordinatesP.comp f) i
  let product := ratMul.comp ((intToRat.comp q).pair u)
  let value := rowCoordinateP f (succIndexP i)
  let z := ratNum.comp (ratSub.comp (product.pair value))
  let positive := OracleSpec.Arithmetic.intLe.comp ((constant code intCode 0).pair q)
  exact (conditional positive z (intNeg.comp z)).congrFun (by intro v; simp [recoveredZ])

/-- A canonical binary positive denominator followed by a framed vector of signed binary
numerators. Only the first row of the returned LLL table is ever decoded. -/
noncomputable def finishP : Procedure frameCode outputCode finish :=
  (intAbs.comp recoveredQP).pair (tabulateBinaryAlongP (0:ℚ) (0:ℤ) coordinatesP recoveredZP)

private theorem mapRange_eq_ofFn {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

theorem rowCoordinatePack {p : ℕ} (u : Fin p → ℚ) (a : ℚ) (D : ℕ)
    (A : Matrix (Fin (p+1)) (Fin (p+1)) ℤ) (j : Fin (p+1)) :
    rowCoordinate ((List.ofFn u,a,D),packedTable A) j.val = unscaleIntegerRow D (A 0) j := by
  have entry (i k : Fin (p+1)) : entryAt (packedTable A) i.val k.val = A i k := by
    unfold entryAt rowAt packedTable
    rw [readAt_ofFn,readAt_ofFn]
  change (entryAt (packedTable A) (0 : Fin (p+1)).val j.val : ℚ) / (D:ℚ) = (A 0 j:ℚ) / D
  rw [entry]

theorem finishPack {p : ℕ} (u : Fin p → ℚ) (a : ℚ) (D : ℕ)
    (A : Matrix (Fin (p+1)) (Fin (p+1)) ℤ) :
    finish ((List.ofFn u,a,D),packedTable A) =
      ((decodeGraphRow a u (unscaleIntegerRow D (A 0))).1,
        List.ofFn (decodeGraphRow a u (unscaleIntegerRow D (A 0))).2) := by
  let f : Frame := ((List.ofFn u,a,D), packedTable A)
  let r := unscaleIntegerRow D (A 0)
  have hq : recoveredQ f = (r 0 / a).num := by
    change (rowCoordinate f 0 / a).num = _
    rw [show rowCoordinate f 0 = r 0 from rowCoordinatePack u a D A 0]
  change ((recoveredQ f).natAbs, (List.range (List.ofFn u).length).map (recoveredZ f)) = _
  rw [List.length_ofFn, mapRange_eq_ofFn, hq]
  change (_, List.ofFn _) = ((r 0/a).num.natAbs,List.ofFn _)
  congr 1
  apply congrArg List.ofFn
  funext i
  have hv : readAt 0 f.1.1 i.val = u i := readAt_ofFn 0 u i
  have hr : rowCoordinate f (i.val+1) = r i.succ := rowCoordinatePack u a D A i.succ
  simp only [recoveredZ,hq,hv,hr]
  rfl

end Selector
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
