import OAI.Computability.BorderVNP.FiniteProcessorEndpoint

/-! # End-to-end field endpoint replay on a live incoming frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamSite TeamSite.Endpoint
open TeamPrivateFragment TeamLocalClock TeamTapeHandoff

variable {w p r k a m g : ℕ} {Q Γ : Type} {F : Type*} [Field F] [Fintype F]

/-- An actual field-weighted loop replay on the just-decoded live bank gives an end-to-end
physical endpoint execution on the original incoming and outgoing streams. Its terminal
sign includes the outgoing frame test and its complete record-emission bank is exposed
to the sorter. -/
theorem live_block (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) (acc accOut : F) (last : Bool) (fits : p ≤ 2^w) (pub : Fin k → Word w) (start z : TeamOpcode.State w p r)
    (H limit elapsed max block' left' elapsed' : Word w) (safe : elapsed ≤ limit)
    (suffix script rest stamp : List Bool) (base : Stacks (Endpoint.Port r k (m*g)))
    (ready : base ∘ startup =
      Startup.input pub H limit max ((Frame.live (packed w start.pc.val) start.reg elapsed).bits ++ suffix))
    (payload : base .payload = []) (steps : ℕ) (sg : Option Bool) (live : Option (Fin p))
    (final : Stacks (TeamSite.Port r k (m*g)))
    (run : StackRuns (replay (loopCode P lib weights)) steps
      ((.clock (some false) (.enter start.pc),Fintype.equivFin F acc), script)
      (installStacks TeamSite.Port.clock (base ∘ Endpoint.Port.site)
        (TeamLocalClock.bank pub start H (packed w (limit.val-elapsed.val)) elapsed max))
      ((.close sg live,Fintype.equivFin F accOut), rest) final)
    (finalClock : ∀ i, final (.clock i) = banks pub z.logged (chargeRegisters block' left' elapsed' 0) max stamp i) :
    ∃ t ≤ Startup.budget r w + 1 + steps + (7*r+40)*(w+1), ∃ out,
      StackRuns (replay (endpointCode P lib weights)) t ((.startup last (Startup.entry p r),Fintype.equivFin F acc),script) base
        ((finishLabel sg (valid (closeMode live) last z.reg elapsed' (base .outgoing)),Fintype.equivFin F accOut),rest) out ∧
      ∀ i, out (.site i) = final i := by
  let f := Frame.live (packed w start.pc.val) start.reg elapsed
  let decoded := Startup.decoded pub f H (packed w (limit.val-elapsed.val)) max suffix
  let mid := installStacks startup base decoded
  obtain ⟨t, ht, first⟩  := FieldProcessor.predecessor_run P lib weights acc last fits pub f H limit max suffix script base ready
  have hv : (packed w start.pc.val).val = start.pc.val := packed_val (lt_of_lt_of_le start.pc.isLt fits)
  have hl : TeamLocalClockPC.lookup p start.pc.val = .live start.pc := by
    simpa only [hv] using TeamLocalClockPC.lookup_packed start.pc fits
  simp only [f, Startup.result, Frame.elapsed, safe, ite_true, hl,
    afterStartup, Startup.remaining, hv, start.pc.isLt, and_self] at first
  have hmid := startup_site base pub start.pc (packed w start.pc.val) start.reg H
    (packed w (limit.val-elapsed.val)) elapsed max suffix
  have body := FieldProcessor.loop_segment P lib weights last run mid hmid
  let endBank := installStacks Endpoint.Port.site mid final
  have aux (i : Endpoint.Port r k (m*g)) (h : ∀ u, Endpoint.Port.site u ≠ i) : endBank i = mid i :=
    installStacks_outside mid final h
  have temp : endBank .tmp = [] := (aux _ (fun _ => by simp)).trans
    (installStacks_at startup_injective base decoded Startup.Port.tmp)
  have stream : endBank .outgoing = base .outgoing := (aux _ (fun _ => by simp)).trans
    (installStacks_outside base decoded (fun u => by cases u <;> simp [startup]))
  have empty : endBank .payload = [] := (aux _ (fun _ => by simp)).trans
    ((installStacks_outside base decoded (fun u => by cases u <;> simp [startup])).trans payload)
  have site (i : TeamSite.Port r k (m*g)) : endBank (.site i) = final i :=
    installStacks_at (fun _ _ h => Endpoint.Port.site.inj h) mid final i
  obtain ⟨time, hb, out, endRun, preserve⟩ := close_run P lib sg live last pub z.logged block' left'
    elapsed' max stamp rest endBank (fun i => (site (.clock i)).trans (finalClock i)) empty temp
  rw [stream] at endRun
  exact ⟨t+steps+time, by omega, out, (first.trans body).trans (close_lift P lib weights accOut endRun), fun i => (preserve i).trans (site i)⟩

end FieldProcessor

end BorderVNP
end Computability
end OAI
