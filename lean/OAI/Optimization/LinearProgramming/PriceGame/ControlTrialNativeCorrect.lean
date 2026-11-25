import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialUniform
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialNative

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open Trial Wire States.Mass Moment TrialExecution

variable {N ne R : ℕ}

theorem boundedTrial_live (hN : 0 < N) (experts : Fin ne → Expert N) (R : ℕ) :
    LiveKernelRefinement probes R experts (boundedTrialKernel (publicTrialGlobals N R experts)) :=
  trialKernelUsing_live concretePrepare concretePrepare_eq hN experts R

/-- Every visited instruction of the checked finite program computes exactly the
reference action for this stack, including both numeric continuations at a query. -/
theorem boundedTrial_guarded (hN : 0 < N) (experts : Fin ne → Expert N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) {tr out}
    (emits : Emits (run R experts (marketSolverAtCommonWeightUnit experts) w hw) tr out) :
    let g := publicTrialGlobals N R experts
    let raw := packetKernel feedbackPrefix N R probes g.2.2
    let good := fun s => step (boundedTrialKernel g) (2*probes) s = step raw (2*probes) s
    ∃ stop, GuardedSteps good raw (2*probes) (initial (depth N) (codeInput (N:=N) 0 (fun _ _ => 0) w))
      tr (nodeTicks (2*probes) (depth N)+tr.length) stop ∧ step raw (2*probes) stop = .halt (codeOutput out.val) :=
  trialKernelUsing_guarded concretePrepare concretePrepare_eq hN experts w hw emits

/-- The source output is obtained by the very transition carried by the concrete
finite Boolean-stack procedure, using the original oracle trace. -/
theorem boundedTrial_halts (hN : 0 < N) (experts : Fin ne → Expert N) (w : Weights ne)
    (hw : ∀ e, 0 ≤ w e) {tr out}
    (emits : Emits (run R experts (marketSolverAtCommonWeightUnit experts) w hw) tr out) :
    let g := publicTrialGlobals N R experts
    ∃ stop, Steps (boundedTrialKernel g) (2*probes) (initial (depth N) (codeInput (N:=N) 0 (fun _ _ => 0) w))
        tr (nodeTicks (2*probes) (depth N)+tr.length) stop ∧
      step (boundedTrialKernel g) (2*probes) stop = .halt (codeOutput out.val) :=
  trialKernelUsing_halts concretePrepare concretePrepare_eq hN experts w hw emits

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
