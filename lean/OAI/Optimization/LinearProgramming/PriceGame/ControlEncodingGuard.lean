import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialGuarded
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingState

/-! Prefix-sensitive numerical guards along a whole first-order traversal. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

universe u
variable {I P R C Q : Type u} {guard : State I P R C → Prop}
  {ops : Kernel I P R C Q} {calls : ℕ} {s t : State I P R C} {tr : List (Q × Bool)} {ticks : ℕ}

/-- Every guard can additionally use a real bounded-length path from the initial state. -/
theorem GuardedSteps.withPrefix (h : GuardedSteps guard ops calls s tr ticks t) :
    GuardedSteps (fun v => guard v ∧ ∃ pre k, Steps ops calls s pre k v ∧ k ≤ ticks)
      ops calls s tr ticks t := by
  induction h with
  | refl s hs => exact .refl _ ⟨hs,[],0,.refl _,le_rfl⟩
  | @silent s next stop tr n safe act tail ih =>
    refine .silent ⟨safe,[],0,.refl _,by omega⟩ act (ih.weaken ?_)
    intro v hv
    obtain ⟨hp,pre,k,walk,hk⟩ := hv
    exact ⟨hp,pre,k+1,.silent act walk,by omega⟩
  | @answer s no yes stop tr n q b safe act tail ih =>
    refine .answer b ⟨safe,[],0,.refl _,by omega⟩ act (ih.weaken ?_)
    intro v hv
    obtain ⟨hp,pre,k,walk,hk⟩ := hv
    exact ⟨hp,(q,b)::pre,k+1,.answer b act walk,by omega⟩

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire
namespace Envelope

open Trial

theorem stateSize_mono (e : Envelope) (calls : ℕ) {k K : ℕ} (hle : k ≤ K) :
    e.stateSize calls k ≤ e.stateSize calls K := by
  unfold stateSize pcSize pairBound
  omega

/-- Element bounds on the marks, and a single bound on the running time, give a uniform
bound on the code of each machine state, including every suspension and its complete stack. -/
theorem guarded_state_length (e : Envelope) {ops : Kernel NodeInput Prepared PackedRound Completed PackedQuery}
    {calls ticks K : ℕ} {i : NodeInput} {tr} {last : State NodeInput Prepared PackedRound Completed}
    (run : GuardedSteps e.StatePayload ops calls (initial e.depth i) tr ticks last) (limit : ticks ≤ K) :
    GuardedSteps (fun s => (stateCode s).length ≤ e.stateSize calls K) ops calls
      (initial e.depth i) tr ticks last :=
  run.withPrefix.weaken fun _ ⟨h,_,_,steps,le⟩ =>
    (e.reachable_state_length steps h).trans (stateSize_mono e calls (le.trans limit))

end Envelope
end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
