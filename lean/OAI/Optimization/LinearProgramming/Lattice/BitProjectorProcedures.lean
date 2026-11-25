import OAI.Computability.QuantumFactoring.BitStackRationalDivision
import OAI.Optimization.LinearProgramming.Lattice.BitProjectorData
import OAI.Optimization.LinearProgramming.Lattice.BitMatrixProcedures
import OAI.Optimization.LinearProgramming.Lattice.BitList
import OAI.Optimization.LinearProgramming.Lattice.BitGuarded

/-! A uniform finite Boolean-stack program for each dense rational projector update. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Projector

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

private noncomputable def lengthP {α : Type} (e : α → List Bool) (d : α) :
    Procedure (listCode e) unaryCode List.length :=
  OAI.Optimization.LinearProgramming.PriceGame.Learning.GenerationCost.lengthUnaryP e d

private noncomputable def atP {α : Type} {ea : α → List Bool} {rs : α → Table} {i j : α → ℕ}
    (A : Procedure ea tableCode rs) (r : Procedure ea Nat.bits i) (c : Procedure ea Nat.bits j) :
    Procedure ea ratCode (fun z => cell (rs z) (i z) (j z)) :=
  (listGet ratCode 0).comp (c.pair ((listGet rowCode []).comp (r.pair A)))

noncomputable def dotP : Procedure (prodCode rowCode rowCode) ratCode (fun p : Row × Row => dot p.1 p.2) := by
  let e := prodCode rowCode rowCode
  let x := first rowCode rowCode
  let y := second rowCode rowCode
  let ctx := second unaryCode e
  let k := unaryToBits.comp (first unaryCode e)
  let a := (listGet ratCode 0).comp (k.pair (x.comp ctx))
  let b := (listGet ratCode 0).comp (k.pair (y.comp ctx))
  let terms := tabulate (f := fun p : Row × Row => fun k => readAt 0 p.1 k * readAt 0 p.2 k) (0:ℚ)
    (ratMul.comp (a.pair b))
  exact PriceGame.Control.Native.ratListSumP.comp (terms.comp (((lengthP ratCode 0).comp x).pair (identity e)))

noncomputable def actP : Procedure (prodCode tableCode rowCode) rowCode (fun p : Table × Row => act p.1 p.2) := by
  let e := prodCode tableCode rowCode
  let A := first tableCode rowCode
  let y := second tableCode rowCode
  let ctx := second unaryCode e
  let i := unaryToBits.comp (first unaryCode e)
  let a := (listGet rowCode []).comp (i.pair (A.comp ctx))
  exact tabulateAlongP (ea := rowCode) (eb := ratCode) [] (0:ℚ)
    (f := fun p : Table × Row => fun k => dot (readAt [] p.1 k) p.2) A
    (dotP.comp (a.pair (y.comp ctx)))

noncomputable def transP : Procedure tableCode tableCode trans := by
  let ij := first (prodCode unaryCode unaryCode) tableCode
  let A := second (prodCode unaryCode unaryCode) tableCode
  let i := unaryToBits.comp ((first unaryCode unaryCode).comp ij)
  let j := unaryToBits.comp ((second unaryCode unaryCode).comp ij)
  exact valueSquareTableP tableCode ratCode 0 (lengthP rowCode []) (f := fun a i j => cell a j i)
    (atP A j i)

noncomputable def identP : Procedure unaryCode tableCode ident := by
  let ij := first (prodCode unaryCode unaryCode) unaryCode
  let i := unaryToBits.comp ((first unaryCode unaryCode).comp ij)
  let j := unaryToBits.comp ((second unaryCode unaryCode).comp ij)
  let env := squareArgCode unaryCode
  let eq := PriceGame.Control.Native.natEqP.comp (i.pair j)
  let entry := conditional eq (constant env ratCode 1) (constant env ratCode 0)
  apply valueSquareTableP unaryCode ratCode 0 (identity unaryCode)
    (f := fun _ i j => if i=j then (1:ℚ) else 0)
  exact entry.congrFun (by rintro ⟨⟨i,j⟩,p⟩; change (if decide (i=j) then _ else _) = _; by_cases h : i=j <;> simp [h])

private abbrev CorrectArg := Table × (Row × (Row × ℚ))
private def correctCode := prodCode tableCode (prodCode rowCode (prodCode rowCode ratCode))

private noncomputable def correctedP : Procedure correctCode tableCode
    (fun a : CorrectArg => corrected a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  let P := first tableCode (prodCode rowCode (prodCode rowCode ratCode))
  let more := second tableCode (prodCode rowCode (prodCode rowCode ratCode))
  let u := (first rowCode (prodCode rowCode ratCode)).comp more
  let rest := (second rowCode (prodCode rowCode ratCode)).comp more
  let r := (first rowCode ratCode).comp rest
  let d := (second rowCode ratCode).comp rest
  let ctx := second (prodCode unaryCode unaryCode) correctCode
  let ij := first (prodCode unaryCode unaryCode) correctCode
  let i := unaryToBits.comp ((first unaryCode unaryCode).comp ij)
  let j := unaryToBits.comp ((second unaryCode unaryCode).comp ij)
  let old := atP (P.comp ctx) i j
  let ui := (listGet ratCode 0).comp (i.pair (u.comp ctx))
  let rj := (listGet ratCode 0).comp (j.pair (r.comp ctx))
  let val := ratSub.comp (old.pair (ratMul.comp ((ratDiv.comp (ui.pair (d.comp ctx))).pair rj)))
  exact valueSquareTableP correctCode ratCode 0 ((lengthP rowCode []).comp P)
    (f := fun a i j => cell a.1 i j - readAt 0 a.2.1 i / a.2.2.2 * readAt 0 a.2.2.1 j) val

private noncomputable def isZeroP : Procedure ratCode boolCode (fun x => decide (x=0)) := by
  let x := identity ratCode
  let z := constant ratCode ratCode 0
  let both := boolAnd.comp ((OracleSpec.Arithmetic.ratLe.comp (x.pair z)).pair (OracleSpec.Arithmetic.ratLe.comp (z.pair x)))
  refine both.congrFun ?_
  intro q
  change (decide (q≤0) && decide (0≤q)) = decide (q=0)
  rcases lt_trichotomy q 0 with h | h | h
  · simp [not_le.mpr h,h.ne]
  · simp [h]
  · simp [not_le.mpr h,h.ne']

/-- All row products, divisions and table construction are built from the fixed
rational arithmetic, list and Boolean-stack procedures. -/
noncomputable def stepP : Procedure (prodCode tableCode intRowCode) tableCode
    (fun a : Table × List ℤ => step a.1 a.2) := by
  let P := first tableCode intRowCode
  let z := second tableCode intRowCode
  let cast := (listMap (0:ℤ) (0:ℚ) intToRat).comp z
  let u := actP.comp (P.pair cast)
  let d := dotP.comp (u.pair u)
  let r := actP.comp ((transP.comp P).pair u)
  let nonzero := correctedP.comp (P.pair (u.pair (r.pair d)))
  refine (conditional (isZeroP.comp d) P nonzero).congrFun ?_
  rintro ⟨A,z⟩
  change (if decide (dot (image A z) (image A z) = 0) then _ else _) = _
  unfold step
  split <;> simp_all
  rfl

noncomputable def startP : Procedure argCode workCode start := by
  let p := first unaryCode intMatrixCode
  let a := second unaryCode intMatrixCode
  exact ((listReverse intRowCode []).comp a).pair (identP.comp p)

noncomputable def nextP : Procedure workCode workCode next := by
  let remain := first intMatrixCode tableCode
  let P := second intMatrixCode tableCode
  let z := (listHead intRowCode []).comp remain
  let tail := (listTail intRowCode).comp remain
  let advance := tail.pair (stepP.comp (P.pair z))
  let empty := (listEmpty intRowCode).comp remain
  exact (conditional empty (identity workCode) advance).congrFun (by rintro ⟨zs,A⟩; cases zs <;> rfl)

end Projector
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
