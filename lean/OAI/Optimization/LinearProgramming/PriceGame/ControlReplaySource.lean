import OAI.Optimization.LinearProgramming.PriceGame.ControlReplayBound
import OAI.Optimization.LinearProgramming.PriceGame.ControlReplayMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignReplay
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignGuardIntersection
import OAI.Optimization.LinearProgramming.PriceGame.ControlExchanges

/-! Refinement of the finite-tape native replay engine to the adaptive public price computation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
namespace Replay

/-- The data-only starting program counter on a fresh public input. -/
def initialPC (i : PublicInput) : Driver.PC :=
  .campaign (startCampaign i.goods i.range i.anchor.val (Campaign.rounds i.goods i.range))

/-- Exact controller ticks before entering the source branch's terminal state. -/
def sourceTicks (i : PublicInput) (len : ℕ) : ℕ :=
  Campaign.rounds i.goods i.range *
    (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth i.goods) + 2) + len

/-- The guard is required only on actual emitted source traces. The final `PC` is guarded as well. -/
def SourceRuns (i : PublicInput) (P : Driver.PC → Prop) : Prop :=
  ∀ {tr b}, Trial.Emits (campaignSolver Campaign.rounds i) tr b →
    ∃ last, Driver.GuardedRun P (initialPC i) tr (sourceTicks i tr.length) last ∧
      Driver.step last = .halt b

theorem sourceTicks_le_fuel {t : Tape} {tr b} (h : Trial.Emits (campaignSolver Campaign.rounds t.input) tr b) :
    sourceTicks t.input tr.length + 1 ≤ fuelPolynomial.eval (ecPad t).length := by
  have hlen := (Driver.emits_length_public h).trans (campaignSolver_height Campaign.rounds t.input)
  exact (Nat.succ_le_succ (Nat.add_le_add_left hlen _)).trans (controlClock_le_fuelPolynomial t)

private theorem map_observation {α β γ δ σ : Type*} (v : α ⊕ β) (f : α → γ) (g : β → δ) (h : γ → σ) :
    v.map (h ∘ f) g = (v.map f g).map h id := by cases v <;> rfl

private theorem short_observe {N : ℕ} {p : Computation N Bool} {tr b}
    (e : Trial.Emits p tr b) (k : ℕ) (hk : k < tr.length) :
    (observe p ((tr.take k).map Prod.snd)).map Prod.fst packQuery = .inr tr[k].1 := by
  change (observe p ((tr.take k).map Prod.snd)).map (Prod.fst ∘ id) packQuery = _
  rw [map_observation, Driver.source_observe_short e k hk]
  rfl

/-- On every reply tape, including an unused suffix or a prefix ending at a query, the
actual native iteration returns the source's next query or concluding Boolean sign. -/
theorem source_agrees (t : Tape) {P : Driver.PC → Prop} (runs : SourceRuns t.input P)
    (micro : ℕ × Driver.PC → Driver.Action)
    (correct : ∀ s, P s → micro (t.input.goods,s) = Driver.step s) :
    (advance micro)^[fuelPolynomial.eval (ecPad t).length]
        (live t.input.goods t.reverseReplies.reverse (initialPC t.input)) =
      .inr ((observe (campaignSolver Campaign.rounds t.input) t.reverseReplies.reverse).map
        Prod.fst packQuery) := by
  obtain ⟨tr,b,emit,coverage⟩ := Driver.fits_source (campaignSolver Campaign.rounds t.input)
    t.reverseReplies.reverse
  obtain ⟨last, run,stop⟩ := runs emit
  have budget := sourceTicks_le_fuel (t:=t) emit
  rcases coverage with ⟨tail,hit⟩ | ⟨k,hk,hit⟩
  · rw [hit,emit.observe_tape tail]
    exact more (complete run.steps t.input.goods correct ((correct _ run.endpoint).trans stop) tail) budget
  · rw [hit,short_observe emit k hk]
    exact more (short run.steps t.input.goods correct k hk) budget

end Replay
end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
