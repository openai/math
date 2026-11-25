import OAI.Optimization.LinearProgramming.Lattice.BitProbeControl
import OAI.Computability.QuantumFactoring.BitStackRationalDivision

/-! The two binary-stack dispatch cases for nonzero residuals and returned ratio bits. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
namespace Probe

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

noncomputable def emitRatioP : Procedure ratioCode actionCode emitRatio := by
  let l := first ratioLeftCode ratioRightCode
  let r := second ratioLeftCode ratioRightCode
  let pivot := (first pivotCode (prodCode intRowCode intMatrixCode)).comp l
  let todo := (second pivotCode (prodCode intRowCode intMatrixCode)).comp l
  let pivotRow := (second paramsCode intRowCode).comp pivot
  let a := (first intRowCode intMatrixCode).comp todo
  let pair := (first counterCode remainingCode).comp r
  let n := (first intCode Nat.bits).comp pair
  let den := natToInt.comp ((second intCode Nat.bits).comp pair)
  let query := combineRowsP.comp ((den.pair n).pair (a.pair pivotRow))
  exact askP query (rightP carryLeftCode (rightP pivotCode (identity ratioCode)))

def nextRowArgCode := prodCode (prodCode pivotCode intMatrixCode) ratListCode

noncomputable def nextRowP : Procedure nextRowArgCode actionCode
    (fun x : (Pivot × IntMatrix) × List ℚ => nextRow x.1.1 x.1.2 x.2) := by
  let l := first (prodCode pivotCode intMatrixCode) ratListCode
  let vals := second (prodCode pivotCode intMatrixCode) ratListCode
  let pivot := (first pivotCode intMatrixCode).comp l
  let rows := (second pivotCode intMatrixCode).comp l
  let pars := (first paramsCode intRowCode).comp pivot
  let dims := (first (prodCode unaryCode unaryCode) intMatrixCode).comp pars
  let k := (second unaryCode unaryCode).comp dims
  let left := pivot.pair (((listHead (ea:=intRowCode) ([]:Row)).comp rows).pair
    ((listTail (ea:=intRowCode)).comp rows))
  let right := (constant nextRowArgCode counterCode ((0:ℤ),(1:ℕ))).pair ((unaryPred.comp k).pair vals)
  let finish := doneP true ((listReverse (ea:=ratCode) (0:ℚ)).comp vals)
  refine (conditional ((emptyListP intRowCode).comp rows) finish (emitRatioP.comp (left.pair right))).congrFun ?_
  rintro ⟨⟨pv,rows⟩,ys⟩
  cases rows <;> rfl

noncomputable def zeroReplyP (answer : Bool) : Procedure pivotCode actionCode (zeroReply answer) := by
  cases answer
  · let empty := constant pivotCode ratListCode ([]:List ℚ)
    let pars := first paramsCode intRowCode
    let dims := (first (prodCode unaryCode unaryCode) intMatrixCode).comp pars
    let k := (second unaryCode unaryCode).comp dims
    let rows := (second (prodCode unaryCode unaryCode) intMatrixCode).comp pars
    let count := (PriceGame.Control.Native.rowSizeP intRowCode ([]:Row)).comp rows
    let noneNeeded := doneP true ((replicateP ratCode 0).comp count)
    let firstRow := nextRowP.comp (((identity pivotCode).pair rows).pair empty)
    refine (conditional (zeroUnaryP.comp k) noneNeeded firstRow).congrFun ?_
    rintro ⟨⟨⟨p,k⟩,rows⟩,d⟩
    by_cases h : k = 0 <;> simp [zeroReply,h,Function.comp_def]
  · exact doneP false (constant pivotCode ratListCode ([]:List ℚ))

noncomputable def ratioReplyP (answer : Bool) : Procedure ratioCode actionCode (ratioReply answer) := by
  let l := first ratioLeftCode ratioRightCode
  let r := second ratioLeftCode ratioRightCode
  let pivot := (first pivotCode (prodCode intRowCode intMatrixCode)).comp l
  let todo := (second pivotCode (prodCode intRowCode intMatrixCode)).comp l
  let rows := (second intRowCode intMatrixCode).comp todo
  let pair := (first counterCode remainingCode).comp r
  let other := (second counterCode remainingCode).comp r
  let n := (first intCode Nat.bits).comp pair
  let den := (second intCode Nat.bits).comp pair
  let left := (first unaryCode ratListCode).comp other
  let vals := (second unaryCode ratListCode).comp other
  let double := intMul.comp ((constant ratioCode intCode (2:ℤ)).pair n)
  let n' := intAdd.comp (double.pair (constant ratioCode intCode (if answer then (1:ℤ) else -1)))
  let d' := binaryMul.comp ((constant ratioCode Nat.bits 2).pair den)
  let next := emitRatioP.comp (l.pair ((n'.pair d').pair ((unaryPred.comp left).pair vals)))
  let value := ratDiv.comp ((intToRat.comp n').pair (natToRat.comp d'))
  let newVals := (listCons (ea:=ratCode)).comp (value.pair vals)
  let advanceRow := nextRowP.comp ((pivot.pair rows).pair newVals)
  refine (conditional (zeroUnaryP.comp left) advanceRow next).congrFun ?_
  intro s
  by_cases h : s.2.2.1 = 0 <;> simp [ratioReply,h,Function.comp_def]

noncomputable def advanceP (answer : Bool) : Procedure carryCode actionCode (advance answer) :=
  (casesSum (casesSum (orientP answer) (compareP answer))
    (casesSum (zeroReplyP answer) (ratioReplyP answer))).congrFun (by
      rintro ((a|b)|(c|d)) <;> rfl)

end Probe
end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
