import OAI.Optimization.LinearProgramming.PriceGame.ControlPhaseMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialStepMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignTransition
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignInnerType
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignGuarded

/-! Attach the physical recursive trial scheduler to the physical weight/learner
campaign step. Each source predicate used for clipping is local to the instruction. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure

def physicalMicro (ops : TrialGlobals → TrialKernel) : ℕ × Driver.PC → Driver.Action :=
  Join.boundedStep (fun z => Trial.step (ops z.1) (2*Moment.probes) z.2) boundedFinish

noncomputable def physicalMicroP (ops : TrialGlobals → TrialKernel) (components : TrialKernelProcedures ops) :
    Procedure (prodCode unaryCode Wire.combinedCode) Join.actionCode (physicalMicro ops) := by
  let trial : Procedure (prodCode Join.globalsCode Wire.stateCode) Join.innerActionCode
      (fun z => Trial.step (ops z.1) (2*Moment.probes) z.2) :=
    (trialStepP _ ops components).congrEncoding (by intro _; rfl) (by intro a; cases a <;> rfl)
  exact Join.boundedStepP trial finishRoundP

def innerAgrees (ops : TrialGlobals → TrialKernel) : Driver.InnerPredicate := fun N R roster s =>
  Trial.step (ops (N,R,roster)) (2*Moment.probes) s = Trial.stepPacket N R Moment.probes roster s

theorem physicalMicro_agrees (ops : TrialGlobals → TrialKernel) (n : ℕ) (pc : Driver.PC)
    (outer : Driver.OuterSafe pc) (dim : Driver.DimensionAt n pc)
    (inner : Driver.InnerHolds (innerAgrees ops) pc) :
    physicalMicro ops (n,pc) = Driver.step pc := by
  apply Join.boundedStep_refines
  · rintro c s rfl
    change c.dimension = n at dim
    subst n
    exact inner
  · rintro c s out rfl edge
    change c.dimension = n at dim
    subst n
    exact boundedFinish_eq c out (outer out edge)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
