import OAI.Optimization.LinearProgramming.PriceGame.ControlReplayLoop
import OAI.Optimization.LinearProgramming.PriceGame.ControlReplaySourceWidth
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignPhysicalComplete
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignWireGuard
import OAI.Optimization.LinearProgramming.OracleSpec.DialogueDeployment

/-! The fixed first-order price-game dispatcher. Its only external input is the dimension,
range and anchor, or a previous finite reply tape and the new answer. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram

def campaignMicro : ℕ × Driver.PC → Driver.Action := physicalMicro boundedTrialKernel

noncomputable def campaignMicroP :
    Procedure (prodCode unaryCode Wire.combinedCode) Join.actionCode campaignMicro :=
  physicalMicroP boundedTrialKernel boundedTrialComponents

/-- The concrete physical replay has one polynomial word bound at every iteration. -/
theorem campaignReplay_width (t : Tape) (j : ℕ) :
    (Replay.stateCode ((Replay.advance campaignMicro)^[j] (Replay.initial t))).length ≤
      (Replay.functionWidth Wire.combinedPolynomial campaignMicroP.bound).eval (ecPad t).length := by
  let agrees : Driver.PC → Prop := fun pc => campaignMicro (t.input.goods,pc) = Driver.step pc
  let bounded : Driver.PC → Prop := fun pc => (Wire.combinedCode pc).length ≤
    Wire.combinedPolynomial.eval (Campaign.inputSize t.input.goods t.input.range)
  have both : Replay.SourceRuns t.input (fun pc => agrees pc ∧ bounded pc) :=
    @Replay.SourceRuns.and t.input agrees bounded
      (@Replay.physicalSourceRuns t.input) (@Wire.campaign_uniform_guard t.input)
  exact Replay.source_width t (P := fun pc => agrees pc ∧ bounded pc) (@both) campaignMicroP
    (fun _ hs => hs.1) Wire.combinedPolynomial (fun _ hs => hs.2) j

/-- The reply tape determines the next public action of the concrete finite state machine. -/
noncomputable def campaignReplay (t : Tape) : Replay.State :=
  (Replay.advance campaignMicro)^[Replay.fuelPolynomial.eval (ecPad t).length] (Replay.initial t)

noncomputable def campaignReplayP : Procedure ecPad Replay.stateCode campaignReplay :=
  OracleSpec.Fuel.boundedReachable Replay.initialP (Replay.advanceP campaignMicroP)
    Replay.fuelPolynomial (Replay.functionWidth Wire.combinedPolynomial campaignMicroP.bound)
    (fun t j _ => campaignReplay_width t j)

theorem campaignReplay_correct (t : Tape) :
    campaignReplay t = .inr (Replay.terminalResult
      (observe (campaignSolver Campaign.rounds t.input) t.reverseReplies.reverse)) :=
  Replay.source_agrees t (P := fun pc => campaignMicro (t.input.goods,pc) = Driver.step pc)
    (@Replay.physicalSourceRuns t.input) campaignMicro (fun _ h => h)

/-- A uniform finite Boolean-stack program for one external dialogue exchange.
The retained data are ordinary bits, the price queries appear in source order,
and all computation between genuine external queries is charged. -/
noncomputable def dispatchProcedure : OracleSpec.Dialogue.ProcedureOf eiPad ecPad
    (dispatch (campaignSolver Campaign.rounds)) :=
  Replay.dialogueOfReplay (campaignSolver Campaign.rounds) campaignReplayP campaignReplay_correct

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
