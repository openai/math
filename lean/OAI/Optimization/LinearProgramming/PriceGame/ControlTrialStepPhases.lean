import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialStepWire

/-! Each phase of the packed control word is compiled independently. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire

abbrev TrialContext := TrialGlobals × List TrialFrame
abbrev trialContextCode : TrialContext → List Bool := prodCode trialGlobalsCode trialStackCode
def blankTrialFrame : TrialFrame := ⟨0,0,default,[],default⟩

private noncomputable def minusOne {α : Type} {e : α → List Bool} {f : α → ℕ}
    (n : Procedure e Nat.bits f) : Procedure e Nat.bits (fun x => f x - 1) :=
  binarySub.comp (n.pair (constant e Nat.bits 1))

private noncomputable def isZero {α : Type} {e : α → List Bool} {f : α → ℕ}
    (n : Procedure e Nat.bits f) : Procedure e boolCode (fun x => decide (f x = 0)) :=
  natEqP.comp (n.pair (constant e Nat.bits 0))

private noncomputable def advanceP := proceedP.comp makeTrialStateP

noncomputable def enterStepP (calls : ℕ) (ops : TrialGlobals → TrialKernel) (pg : TrialKernelProcedures ops) :
    Procedure (prodCode enterDataCode trialContextCode) trialActionCode
      (fun x => step (ops x.2.1) calls ⟨.enter x.1.1 x.1.2,x.2.2⟩) := by
  let same := prodCode enterDataCode trialContextCode
  let payload := first enterDataCode trialContextCode
  let ctx := second enterDataCode trialContextCode
  let n := (first Nat.bits nodeInputCode).comp payload
  let i := (second Nat.bits nodeInputCode).comp payload
  let g := (first trialGlobalsCode trialStackCode).comp ctx
  let stk := (second trialGlobalsCode trialStackCode).comp ctx
  let result := returnPCP.comp (pg.leafP.comp (g.pair i))
  let begin := schedulePCP.comp ((minusOne n).pair ((constant same Nat.bits calls).pair
    (i.pair (constant same trialRowsCode []))))
  apply (conditional (isZero n) (advanceP.comp (result.pair stk)) (advanceP.comp (begin.pair stk))).congrFun
  rintro ⟨⟨k,i⟩,g,stk⟩
  cases k <;> rfl

noncomputable def scheduleStepP (calls : ℕ) (ops : TrialGlobals → TrialKernel) (pg : TrialKernelProcedures ops) :
    Procedure (prodCode scheduleDataCode trialContextCode) trialActionCode
      (fun x => step (ops x.2.1) calls ⟨.schedule x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2,x.2.2⟩) := by
  let payload := first scheduleDataCode trialContextCode
  let ctx := second scheduleDataCode trialContextCode
  let fuel := (first Nat.bits (prodCode Nat.bits trialCallDataCode)).comp payload
  let tail := (second Nat.bits (prodCode Nat.bits trialCallDataCode)).comp payload
  let rem := (first Nat.bits trialCallDataCode).comp tail
  let args := (second Nat.bits trialCallDataCode).comp tail
  let i := (first nodeInputCode trialRowsCode).comp args
  let rows := (second nodeInputCode trialRowsCode).comp args
  let g := (first trialGlobalsCode trialStackCode).comp ctx
  let stk := (second trialGlobalsCode trialStackCode).comp ctx
  let result := returnPCP.comp (pg.assembleP.comp (g.pair args))
  let prep := pg.prepareP.comp (g.pair args)
  let input := pg.descendP.comp (g.pair (i.pair prep))
  let child := enterPCP.comp (fuel.pair input)
  let frame := makeTrialFrameP.comp (fuel.pair ((minusOne rem).pair (i.pair (rows.pair prep))))
  let frames := (listCons frameCode).comp (frame.pair stk)
  apply (conditional (isZero rem) (advanceP.comp (result.pair stk)) (advanceP.comp (child.pair frames))).congrFun
  rintro ⟨⟨fuel,rem,i,rows⟩,g,stk⟩
  cases rem <;> rfl

noncomputable def returnedStepP (calls : ℕ) (ops : TrialGlobals → TrialKernel) :
    Procedure (prodCode packedRoundCode trialContextCode) trialActionCode
      (fun x => step (ops x.2.1) calls ⟨.returned x.1,x.2.2⟩) := by
  let same := prodCode packedRoundCode trialContextCode
  let result := first packedRoundCode trialContextCode
  let stk := (second trialGlobalsCode trialStackCode).comp (second packedRoundCode trialContextCode)
  let head := (listHead frameCode blankTrialFrame).comp stk
  let tail := (listTail frameCode).comp stk
  let scan := feedbackPCP.comp (head.pair (result.pair (constant same id [])))
  apply (conditional ((listEmpty frameCode).comp stk) (haltTrialP.comp result) (advanceP.comp (scan.pair tail))).congrFun
  rintro ⟨out,g,stk⟩
  cases stk <;> rfl

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
