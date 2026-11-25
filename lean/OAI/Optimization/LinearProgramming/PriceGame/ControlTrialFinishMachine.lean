import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialGainMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlBoundedFeedback

/-! The complete physical feedback primitive on a suspended packed child. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire

def boundedTrialFinish (g : TrialGlobals) (input : NodeInput) (_rows : List Completed) (prep : Prepared)
    (child : PackedRound) (bits : List Bool) : Completed ⊕ PackedQuery :=
  if prep.isProbe then (boundedFeedback (input.history,prep.baseline,child.prices,bits)).map
    (boundedChildReturn g.2.2 prep child) id
  else .inl (boundedChildReturn g.2.2 prep child [])

private abbrev FinishArgs := TrialGlobals × NodeInput × List Completed × Prepared × PackedRound × List Bool
private abbrev ec : FinishArgs → List Bool := prodCode trialGlobalsCode trialFinishDataCode
private noncomputable def leftResult : Procedure completedCode trialFinishResultCode
    (Sum.inl : Completed → Completed ⊕ PackedQuery) :=
  (prepend completedCode [false]).result (by intro _; rfl)
private noncomputable def rightResult : Procedure packedQueryCode trialFinishResultCode
    (Sum.inr : PackedQuery → Completed ⊕ PackedQuery) :=
  (prepend packedQueryCode [true]).result (by intro _; rfl)

noncomputable def boundedTrialFinishP : Procedure ec trialFinishResultCode
    (fun x => boundedTrialFinish x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := by
  let g := first trialGlobalsCode trialFinishDataCode
  let rs := (second unaryCode (prodCode Nat.bits assemblyRosterCode)).comp g
  let roster := (second Nat.bits assemblyRosterCode).comp rs
  let data := second trialGlobalsCode trialFinishDataCode
  let childBits := prodCode packedRoundCode (id : List Bool → List Bool)
  let prcb := prodCode preparedCode childBits
  let i := (first nodeInputCode (prodCode trialRowsCode prcb)).comp data
  let a := (second nodeInputCode (prodCode trialRowsCode prcb)).comp data
  let b := (second trialRowsCode prcb).comp a
  let prep := (first preparedCode childBits).comp b
  let os := (second preparedCode childBits).comp b
  let ch := (first packedRoundCode id).comp os
  let bits := frameRepliesP.comp ((second packedRoundCode id).comp os)
  let child := prodCode assemblyRosterCode (prodCode preparedCode packedRoundCode)
  let payload := roster.pair (prep.pair ch)
  let retCtx := second answerListCode child
  let ex := (first assemblyRosterCode (prodCode preparedCode packedRoundCode)).comp retCtx
  let pc := (second assemblyRosterCode (prodCode preparedCode packedRoundCode)).comp retCtx
  let p := (first preparedCode packedRoundCode).comp pc
  let o := (second preparedCode packedRoundCode).comp pc
  let ys := first answerListCode child
  let finish := leftResult.comp (boundedChildReturnP.comp (ex.pair (p.pair (o.pair ys))))
  let request := rightResult.comp (first packedQueryCode child)
  let branching := choosePacket ([] : List Bool) (default : PackedQuery) finish request
  let feedback := boundedFeedbackP.comp ((nodeHistoryP.comp i).pair ((preparedBaselineP.comp prep).pair
    ((roundPricesP.comp ch).pair bits)))
  let whenProbe := branching.comp (feedback.pair payload)
  let whenFinal := leftResult.comp (boundedChildReturnP.comp
    (roster.pair (prep.pair (ch.pair (constant ec answerListCode [])))))
  apply (conditional (preparedKindP.comp prep) whenProbe whenFinal).congrFun
  rintro ⟨g,i,xs,pr,o,w⟩
  change (if pr.isProbe then Sum.elim _ _ (boundedFeedback (i.history,pr.baseline,o.prices,w)) else _) = _
  unfold boundedTrialFinish
  cases pr.isProbe with
  | false => rfl
  | true => cases boundedFeedback (i.history,pr.baseline,o.prices,w) <;> rfl

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
