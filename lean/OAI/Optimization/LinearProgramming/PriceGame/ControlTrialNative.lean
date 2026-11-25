import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialNativeBase
import OAI.Optimization.LinearProgramming.PriceGame.ControlPrepareConcrete

/-! The uniform finite recursive stack instruction with the actual binary
transshipment clearing procedure installed. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire

def boundedTrialKernel : TrialGlobals → TrialKernel := trialKernelUsing concretePrepare

noncomputable def boundedTrialComponents : TrialKernelProcedures boundedTrialKernel :=
  trialComponentsUsing concretePrepareP

/-- Its program and polynomial clock are fixed, uniformly over all input
dimensions, price ranges, expert rosters, oracle replies and saved stacks. -/
noncomputable def boundedTrialStepP : Procedure (prodCode trialGlobalsCode stateCode) trialActionCode
    (fun x => step (boundedTrialKernel x.1) (2*Moment.probes) x.2) :=
  trialStepP (2*Moment.probes) boundedTrialKernel boundedTrialComponents

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
