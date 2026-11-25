import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialRefinementBase
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialPrepare

/-! Unconditional specialization of the explicit packed stack to the LCM transshipment procedure. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States States.Mass Moment TrialExecution

variable {N ne : ℕ}

theorem preparationMatches (r : ℕ) (experts : Fin ne → Expert N) : PreparationMatches r experts where
  probe := fun w hw hist hz xs hj => prepare_probe_spec experts w hw hist hz xs hj
  final := fun w hist xs hj => prepare_final_spec experts w hist xs hj

/-- Principal entry point. The packed roster, query rows, and replies constitute
the entire external interface. -/
theorem run_common_refines {R : ℕ} (experts : Fin ne → Expert N) (w : Weights ne)
    (hw : ∀ e, 0 ≤ w e) {tr out}
    (e : Emits (TrialExecution.run R experts (marketSolverAtCommonWeightUnit experts) w hw) tr out) :
    Evaluates (packetKernel feedbackPrefix N R probes (List.ofFn fun e => packExpert (experts e)))
      (2*probes) (.node (depth N) (codeInput (N:=N) 0 (fun _ _ => 0) w)) tr (codeOutput out.val) := by
  simp only [packetKernel, List.length_ofFn]
  exact execute_common_refines_of_prepare probes R experts (preparationMatches probes experts) (depth N) (l:=0) .root (fun _ _ => 0) w hw
    (fun _ _ _ => rfl) rfl e

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
