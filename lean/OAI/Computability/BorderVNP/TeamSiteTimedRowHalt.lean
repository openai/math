import OAI.Computability.BorderVNP.TeamSiteTimedRowStart
import OAI.Computability.BorderVNP.TeamSiteProcessorRowHalt

/-! # The timed physical processor row after its predecessor has halted -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor.Row

open VPVNP RAMTape RAMTape.PublicExprMachine BurstRAM TeamLocalClock TeamPrivateFragment TeamTapeHandoff
open private step_unique from OAI.Computability.BorderVNP.TeamContractionReplayRun
open private step_next from OAI.Computability.BorderVNP.TeamSiteClockPhases
open private post_step replay_successors from OAI.Computability.BorderVNP.TeamSiteTimedPostlude

/-- Remove a deterministic prefix from a longer trace ending at a halt. -/
private theorem suffix_to_halt {K Q : Type*} [DecidableEq K] {C : StackCode K Q}
    {p n : ℕ} {q a start b last c sign}
    (head : StackRuns C p q a start b) (full : StackRuns C n q a last c) (halt : C last = .halt sign) :
    ∃ t, p+t = n ∧ StackRuns C t start b last c := by
  induction head generalizing n with
  | nil => exact ⟨n,Nat.zero_add _,full⟩
  | cons first _ ih =>
    cases full with
    | nil => cases first <;> simp_all
    | cons second rest =>
      obtain ⟨rfl,rfl⟩ := step_unique first second
      obtain ⟨t,ht,run⟩ := ih rest
      exact ⟨t,by omega,run⟩

variable {Q Γ : Type} {p r k a m g n d e w : ℕ} {P : TeamOpcode.Program p r k a}
variable {lib : Fin a → Macro Q Γ m g} {mark : Fin a → Γ}
variable (X : Site P lib mark n d e w)
local notation "old" => Processor.code P (fun j => extend (lib j) (mark j))
local notation "initial" => TrustedClock.installed (Layout.input (r:=r) (k:=k) (d:=(m+1)*g)) X.raw

private theorem ends_in_postlude {t s s' z z'}
    (run : StackRuns (replay old) t z s z' s') (start : postlude P z.1) : postlude P z'.1 := by
  induction run with
  | nil => exact start
  | @cons q s q' s' _ _ _ step _ ih =>
    apply ih
    exact step_next step (replay_successors (postlude P) (old q.1) q.2 (post_step P lib mark q.1 start))

/-- A halted incoming frame is propagated and checked on the real metered machine,
including bad elapsed clocks, incorrect outgoing frames and failed sorter checks.
The physical prefix and postlude have exactly the original combined tick count. -/
theorem halted_model (elapsed : Word w) (frame : X.frame = .accepted elapsed) :
    Model X [] (some false)
      (Endpoint.haltValid X.last r elapsed X.limit (X.base .outgoing) = true ∧ X.sorted [])
      (X.cost 0 []) := by
  obtain ⟨t,ht,q,out,b,full,halt,valid,checked,sign⟩ := X.halted_model elapsed frame
  obtain ⟨_,_,oldStart,newStart⟩ := decoded_start X []
  have stop : replay old (q,[]) = .halt b := by simp [replay,halt]
  obtain ⟨length,add,tail⟩ := suffix_to_halt oldStart full stop
  have beginPost : postlude P (Processor.Label.block (Q:=Q) (m:=m+1) (g:=g)
      (Endpoint.afterStartup X.last (Startup.result p X.frame X.limit))) := by
    rw [frame]
    by_cases ok : elapsed ≤ X.limit <;> simp [Startup.result,Frame.elapsed,ok,Endpoint.afterStartup,postlude]
  have terminal := ends_in_postlude tail beginPost
  have suffix := postlude_run P lib mark tail beginPost initial
  refine ⟨_,add ▸ ht,.site q,_,b,newStart.trans suffix,?_,valid,?_,sign⟩
  · rw [site_row P lib mark q (fun last sg j pc eq => by subst q; exact terminal),halt]
    rfl
  · intro z
    simpa only [Checked,Processor.Row.Checked,Label.site.injEq] using checked z

end TeamSite.TimedProcessor.Row

end BorderVNP
end Computability
end OAI
