import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialStepMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialFinishMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlLeafMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyMachine

/-! A complete, uniform, finite bit-stack instruction for the recursive trial.
The run-time input contains only finite words describing public and saved data. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire

/-- The market-preparation primitive receives the fixed probe count. The external
controller retains the independent input price range for the leaf operation. -/
def prepareGlobals (g : TrialGlobals) : TrialGlobals := (g.1,Moment.probes,g.2.2)

noncomputable def prepareGlobalsP : Procedure trialGlobalsCode trialGlobalsCode prepareGlobals := by
  let n := first unaryCode (prodCode Nat.bits assemblyRosterCode)
  let rest := second unaryCode (prodCode Nat.bits assemblyRosterCode)
  let experts := (second Nat.bits assemblyRosterCode).comp rest
  exact n.pair ((constant trialGlobalsCode Nat.bits Moment.probes).pair experts)

abbrev PrepareWords := TrialGlobals × NodeInput × List Completed

def trialKernelUsing (preparePacket : PrepareWords → Prepared) (g : TrialGlobals) : TrialKernel where
  leaf := leafPacketSized g
  prepare := fun i rows => preparePacket (prepareGlobals g,i,rows)
  childInput := descend
  assemble := fun i rows => assembleValue Moment.probes ⟨g.2.2,i,rows⟩
  finish := boundedTrialFinish g

private noncomputable def assembleFromGlobalsP (r : ℕ) :
    Procedure (prodCode trialGlobalsCode trialCallDataCode) packedRoundCode
      (fun x => assembleValue r ⟨x.1.2.2,x.2.1,x.2.2⟩) := by
  let g := first trialGlobalsCode trialCallDataCode
  let tail := (second unaryCode (prodCode Nat.bits assemblyRosterCode)).comp g
  let ex := (second Nat.bits assemblyRosterCode).comp tail
  let rows := second trialGlobalsCode trialCallDataCode
  exact ((assembleFieldsP r).comp (ex.pair rows)).congrFun (fun _ => rfl)

noncomputable def trialComponentsUsing {preparePacket : PrepareWords → Prepared}
    (prepareCode : Procedure (prodCode trialGlobalsCode trialCallDataCode) preparedCode preparePacket) :
    TrialKernelProcedures (trialKernelUsing preparePacket) where
  leafP := leafPacketSizedP
  prepareP := prepareCode.comp ((prepareGlobalsP.comp (first trialGlobalsCode trialCallDataCode)).pair
    (second trialGlobalsCode trialCallDataCode))
  descendP := trialDescendP
  assembleP := by
    change Procedure (prodCode trialGlobalsCode trialCallDataCode) packedRoundCode
      (fun x => assembleValue Moment.probes ⟨x.1.2.2,x.2.1,x.2.2⟩)
    exact assembleFromGlobalsP Moment.probes
  finishP := boundedTrialFinishP

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
