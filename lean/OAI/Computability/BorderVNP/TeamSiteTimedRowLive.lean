import OAI.Computability.BorderVNP.TeamSiteTimedRowFinish

/-! # From a timed native live chunk to the actual physical sorter verdict -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor.Row

open VPVNP RAMTape RAMTape.PublicExprMachine BurstRAM TeamLocalClock TeamPrivateFragment TeamTapeHandoff
open TeamSiteChoices TeamSiteEvents SupplyRun

variable {Q Γ : Type} {p r k a m g n d e w : ℕ} {P : TeamOpcode.Program p r k a}
variable {lib : Fin a → Macro Q Γ m g} {mark : Fin a → Γ}
variable (X : Site P lib mark n d e w)
local notation "oldLib" => fun j => extend (lib j) (mark j)
local notation "N" => X.raw.length^25

/-- A closed chronological row is realized by the trusted processor from its
actual initialized bank through every signed private call, successor comparison,
record closure and both possible physical sorter lanes. -/
theorem live_model (s z : TeamOpcode.State w p r) (elapsed : Word w)
    (inputFrame : X.frame = .live (packed w s.pc.val) s.reg elapsed) (safe : elapsed ≤ X.limit)
    (es : List (TeamRAM.Event w)) (fin : Window w) (live : Option (Fin p))
    (chunk : Chunk (P.fetch X.pub (fun j => (lib j).timedEval (mark j) N)) s (X.window elapsed) es z fin)
    (closed : Closed P X.pub z fin live) :
    Model X (chunkBits es) (chunkSign (some false) es)
      (X.guard (Finish.frame (TeamSite.Endpoint.closeMode live) z.reg fin.elapsed) = true ∧ X.sorted es)
      (budget X N es) := by
  let sg := chunkSign (some false) es
  let body := TimedBudget.body m g (TimedBudget.meterCoefficient m g) N es
  obtain ⟨t,ht,pre,read,meter⟩ := start_live X s elapsed inputFrame safe (chunkBits es)
  have sc := X.windowSafe elapsed safe
  have cr : startBank X ∘ loopPort ∘ TeamSite.Port.clock = (X.window elapsed).bank X.pub s := by
    rw [← Function.comp_assoc,read]; exact X.loopBank_clock ..
  obtain ⟨t',out,ht',ch,wr,cb,fr⟩ := TimedProcessor.close_complete P X.pub lib mark N X.last chunk live closed
    (some false) X.initial (startBank X) [] sc cr (read ▸ X.loopBank_work s elapsed) meter X.space
  rw [List.append_nil] at ch
  let ordinary := out ∘ TeamClocked.Port.user
  let localBank := ordinary ∘ Processor.endpoint
  obtain ⟨stream,payload,tmp⟩ := endpoint_streams X fr
  have fc : fin.cap = X.cap := (chunk.clock sc).2.2.2.2.2.2
  obtain ⟨time,htime,b,endRun,preserve⟩ := TeamSite.Endpoint.close_run P oldLib sg live X.last X.pub z.logged
    fin.block fin.global fin.elapsed X.cap [] [] localBank (fun i => by rw [← fc]; exact congrFun cb i) payload tmp
  rw [show localBank .outgoing = X.base .outgoing from stream] at endRun
  let after := installStacks Processor.endpoint ordinary b
  let full := installStacks TeamClocked.Port.user out after
  have ep := Processor.endpoint_replay P oldLib endRun ordinary rfl
  have post := postlude_run P lib mark ep (by trivial) out
  rw [installStacks_eq (fun _ _ => TeamClocked.Port.user.inj) out ordinary (fun _ => rfl)] at post
  have underlying : full ∘ TeamClocked.Port.user = after :=
    funext fun i => installStacks_at (fun _ _ => TeamClocked.Port.user.inj) out after i
  have route : Processor.RouteReady n X.fields X.primary X.secondary ordinary := by
    dsimp only [ordinary]
    rw [← endpoint_frame X fr]
    exact X.route.installEndpoint localBank
  have hb : RecordBuffer.Holds X.hw₂ (2^e) (X.slots es) (full ∘ TeamClocked.Port.user ∘ Layout.buffer) := by
    have same : full ∘ TeamClocked.Port.user ∘ Layout.buffer = (out ∘ loopPort) ∘ probe ∘ TeamProbeEmit.Port.buffer := by
      funext i
      exact (congrFun underlying (Layout.buffer i)).trans ((installStacks_at Processor.endpoint_injective ordinary b
        (.site (probe (.buffer i)))).trans (preserve (probe (.buffer i))))
    rw [same,Processor.Row.Context.slots,inputFrame]
    exact wr.buffer
  rw [X.guard_frame]
  apply finish X es sg _ body _ ((pre.trans ch).trans post) (underlying ▸ route.installEndpoint b) hb
  change t' ≤ body at ht'
  unfold Processor.Budget.endpoint
  have hc := Nat.mul_le_mul_right (w+1) (show 7*r+40 ≤ 7*r+45 by omega)
  omega

end TeamSite.TimedProcessor.Row

end BorderVNP
end Computability
end OAI
