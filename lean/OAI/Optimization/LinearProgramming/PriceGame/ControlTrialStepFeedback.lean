import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialStepPhases

/-! The feedback return instruction either commits one cached child packet or
constructs the two saved-data continuations of the pending public query. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire

abbrev FeedbackContext := FeedbackData × TrialContext
abbrev trialFeedbackContextCode : FeedbackContext → List Bool := prodCode feedbackDataCode trialContextCode

def commitTrialChild (v : Completed × FeedbackContext) : TrialAction :=
  let f := v.2.1.1
  .proceed ⟨.schedule f.childFuel f.remaining f.input (f.prefix++[v.1]),v.2.2.2⟩

noncomputable def commitTrialChildP :
    Procedure (prodCode completedCode trialFeedbackContextCode) trialActionCode commitTrialChild := by
  let env := prodCode completedCode trialFeedbackContextCode
  let c := first completedCode trialFeedbackContextCode
  let ctx := second completedCode trialFeedbackContextCode
  let obs := (first feedbackDataCode trialContextCode).comp ctx
  let global := (second feedbackDataCode trialContextCode).comp ctx
  let stk := (second trialGlobalsCode trialStackCode).comp global
  let f := trialFrameViewP.comp ((first frameCode (prodCode packedRoundCode id)).comp obs)
  let fuel := (first Nat.bits (prodCode Nat.bits (prodCode nodeInputCode (prodCode trialRowsCode preparedCode)))).comp f
  let r := (second Nat.bits (prodCode Nat.bits (prodCode nodeInputCode (prodCode trialRowsCode preparedCode)))).comp f
  let rem := (first Nat.bits (prodCode nodeInputCode (prodCode trialRowsCode preparedCode))).comp r
  let ixs := (second Nat.bits (prodCode nodeInputCode (prodCode trialRowsCode preparedCode))).comp r
  let i := (first nodeInputCode (prodCode trialRowsCode preparedCode)).comp ixs
  let rest := (second nodeInputCode (prodCode trialRowsCode preparedCode)).comp ixs
  let xs := (first trialRowsCode preparedCode).comp rest
  let one := (listCons completedCode).comp (c.pair (constant env trialRowsCode []))
  let rows := (listAppend completedCode default).comp (xs.pair one)
  let pc := schedulePCP.comp (fuel.pair (rem.pair (i.pair rows)))
  exact proceedP.comp (makeTrialStateP.comp (pc.pair stk))

def suspendTrialChild (v : PackedQuery × FeedbackContext) : TrialAction :=
  let (q,(frame,out,tape),_,stk) := v
  .ask q ⟨.feedback frame out (tape++[false]),stk⟩ ⟨.feedback frame out (tape++[true]),stk⟩

noncomputable def suspendTrialChildP :
    Procedure (prodCode packedQueryCode trialFeedbackContextCode) trialActionCode suspendTrialChild := by
  let env := prodCode packedQueryCode trialFeedbackContextCode
  let query := first packedQueryCode trialFeedbackContextCode
  let ctx := second packedQueryCode trialFeedbackContextCode
  let obs := (first feedbackDataCode trialContextCode).comp ctx
  let global := (second feedbackDataCode trialContextCode).comp ctx
  let stk := (second trialGlobalsCode trialStackCode).comp global
  let frame := (first frameCode (prodCode packedRoundCode id)).comp obs
  let cb := (second frameCode (prodCode packedRoundCode id)).comp obs
  let out := (first packedRoundCode id).comp cb
  let bits := (second packedRoundCode id).comp cb
  let resume (b : Bool) := makeTrialStateP.comp
    ((feedbackPCP.comp (frame.pair (out.pair (Procedure.append.comp (bits.pair (constant env id [b])))))).pair stk)
  exact askTrialP.comp (query.pair ((resume false).pair (resume true)))

noncomputable def feedbackStepP (calls : ℕ) (ops : TrialGlobals → TrialKernel) (pg : TrialKernelProcedures ops) :
    Procedure trialFeedbackContextCode trialActionCode
      (fun x => step (ops x.2.1) calls ⟨.feedback x.1.1 x.1.2.1 x.1.2.2,x.2.2⟩) := by
  let obs := first feedbackDataCode trialContextCode
  let global := second feedbackDataCode trialContextCode
  let g := (first trialGlobalsCode trialStackCode).comp global
  let f := trialFrameViewP.comp ((first frameCode (prodCode packedRoundCode id)).comp obs)
  let tail := (second Nat.bits (prodCode Nat.bits (prodCode nodeInputCode (prodCode trialRowsCode preparedCode)))).comp f
  let ixs := (second Nat.bits (prodCode nodeInputCode (prodCode trialRowsCode preparedCode))).comp tail
  let i := (first nodeInputCode (prodCode trialRowsCode preparedCode)).comp ixs
  let ds := (second nodeInputCode (prodCode trialRowsCode preparedCode)).comp ixs
  let xs := (first trialRowsCode preparedCode).comp ds
  let prep := (second trialRowsCode preparedCode).comp ds
  let result := (second frameCode (prodCode packedRoundCode id)).comp obs
  let done := pg.finishP.comp (g.pair (i.pair (xs.pair (prep.pair result))))
  let branch := choosePacket (default : Completed) (default : PackedQuery) commitTrialChildP suspendTrialChildP
  apply (branch.comp (done.pair (identity trialFeedbackContextCode))).congrFun
  rintro ⟨⟨f,out,tape⟩,g,stk⟩
  change Sum.elim _ _ ((ops g).finish f.input f.prefix f.prepared out tape) = _
  simp only [step]
  cases (ops g).finish f.input f.prefix f.prepared out tape <;> rfl

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
