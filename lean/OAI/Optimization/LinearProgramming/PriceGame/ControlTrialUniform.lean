import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialLiveParts

/-! The complete arbitrary-reply run and returned packet depend on the local
numerical market specification. The concrete market discharges it in NativeCorrect. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open Trial Wire States.Mass Moment TrialExecution

variable {N ne R : ℕ}

/-- The precise local contract of the capped numerical market operation. -/
abbrev PrepareAgrees (preparePacket : PrepareWords → Prepared) : Prop :=
  ∀ x : PrepareWords, x.1.1*2^x.2.1.level ≤ 2*(x.1.1*x.1.1) →
    (∀ i < x.1.2.2.length, scoreTotal x.2.2 i ≤ 2*probes*(2*x.1.1)^274) →
    preparePacket x = preparePacketSized x.1.1 x.1.2.1 x.1.2.2.length x.1.2.2 x.2.1 x.2.2

/-- Every visited stack instruction computes the reference action, including both
numeric continuations at a query, when the preparation satisfies its local contract. -/
theorem trialKernelUsing_guarded (preparePacket : PrepareWords → Prepared) (hc : PrepareAgrees preparePacket)
    (hN : 0 < N) (experts : Fin ne → Expert N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) {tr out}
    (emits : Emits (run R experts (marketSolverAtCommonWeightUnit experts) w hw) tr out) :
    let g := publicTrialGlobals N R experts
    let raw := packetKernel feedbackPrefix N R probes g.2.2
    let good := fun s => step (trialKernelUsing preparePacket g) (2*probes) s = step raw (2*probes) s
    ∃ stop, GuardedSteps good raw (2*probes) (initial (depth N) (codeInput (N:=N) 0 (fun _ _ => 0) w))
      tr (nodeTicks (2*probes) (depth N)+tr.length) stop ∧ step raw (2*probes) stop = .halt (codeOutput out.val) :=
  (trialKernelUsing_live preparePacket hc hN experts R).guarded w hw emits

/-- The resulting numeric stack follows the original oracle trace and returns
the same prices, scores, and nested probe log. -/
theorem trialKernelUsing_halts (preparePacket : PrepareWords → Prepared) (hc : PrepareAgrees preparePacket)
    (hN : 0 < N) (experts : Fin ne → Expert N) (w : Weights ne)
    (hw : ∀ e, 0 ≤ w e) {tr out}
    (emits : Emits (run R experts (marketSolverAtCommonWeightUnit experts) w hw) tr out) :
    let g := publicTrialGlobals N R experts
    ∃ stop, Steps (trialKernelUsing preparePacket g) (2*probes) (initial (depth N) (codeInput (N:=N) 0 (fun _ _ => 0) w))
        tr (nodeTicks (2*probes) (depth N)+tr.length) stop ∧
      step (trialKernelUsing preparePacket g) (2*probes) stop = .halt (codeOutput out.val) := by
  obtain ⟨stop,run,done⟩ := trialKernelUsing_guarded preparePacket hc hN experts w hw emits
  exact ⟨stop,(run.changeKernel (fun _ he => he)).forget,run.stop.trans done⟩

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
