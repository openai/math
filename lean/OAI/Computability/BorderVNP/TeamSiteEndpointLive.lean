import OAI.Computability.BorderVNP.TeamSiteEndpointRuns

/-!
# A complete processor block on a live incoming frame

The actual predecessor decoder installs the public words and received registers
directly into the signed-loop bank. Its retained successor candidate and fresh
workspace then serve the physical closing check. A replay of the guarded inner
loop composes with both endpoints using the identical sequence of choice bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Endpoint

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamPrivateFragment TeamLocalClock TeamTapeHandoff

variable {w p r k a m g d : ℕ} {Q Γ : Type}

/-- Installing a decoded live frame changes just the clock and architectural registers
inside the signed-loop bank. In particular the initialized record buffer is preserved. -/
theorem startup_site (base : Stacks (Port r k d)) (pub : Fin k → Word w)
    (pc : Fin p) (word : Word w) (regs : Fin r → Word w) (H left elapsed max : Word w) (suffix : List Bool) :
    let decoded := Startup.decoded pub (.live word regs elapsed) H left max suffix
    (installStacks startup base decoded) ∘ Port.site =
      installStacks TeamSite.Port.clock (base ∘ Port.site) (TeamLocalClock.bank pub ⟨pc,regs⟩ H left elapsed max) := by
  intro decoded
  funext i
  cases i with
  | clock j =>
    exact ((installStacks_at startup_injective base decoded (.clock j)).trans
      (Startup.decoded_clock pub pc word elapsed regs H left max suffix j)).trans
      (installStacks_at (fun _ _ he => TeamSite.Port.clock.inj he) _ _ j).symm
  | _ =>
    change installStacks startup base decoded _ = _
    rw [installStacks_outside (hl := fun u => by cases u <;> simp [startup])]
    rw [installStacks_outside (hl := fun _ => by simp)]
    rfl

/-- An actual signed-loop replay on the just-decoded live bank gives an end-to-end
physical endpoint execution on the original incoming and outgoing streams. Its terminal
sign includes the outgoing frame test and its complete record-emission bank is exposed
to the sorter. -/
theorem live_block (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (last : Bool) (fits : p ≤ 2^w) (pub : Fin k → Word w) (start z : TeamOpcode.State w p r)
    (H limit elapsed max block' left' elapsed' : Word w) (safe : elapsed ≤ limit)
    (suffix script rest stamp : List Bool) (base : Stacks (Port r k (m*g)))
    (ready : base ∘ startup =
      Startup.input pub H limit max ((Frame.live (packed w start.pc.val) start.reg elapsed).bits ++ suffix))
    (payload : base .payload = []) (steps : ℕ) (sg : Option Bool) (live : Option (Fin p))
    (final : Stacks (TeamSite.Port r k (m*g)))
    (run : StackRuns (replay (TeamSite.Loop.code P lib)) steps
      (.clock (some false) (.enter start.pc), script)
      (installStacks TeamSite.Port.clock (base ∘ Port.site)
        (TeamLocalClock.bank pub start H (packed w (limit.val-elapsed.val)) elapsed max))
      (.close sg live, rest) final)
    (finalClock : ∀ i, final (.clock i) = banks pub z.logged (chargeRegisters block' left' elapsed' 0) max stamp i) :
    ∃ t ≤ Startup.budget r w + 1 + steps + (7*r+40)*(w+1), ∃ out,
      StackRuns (replay (code P lib)) t (.startup last (Startup.entry p r),script) base
        (finishLabel sg (valid (closeMode live) last z.reg elapsed' (base .outgoing)),rest) out ∧
      ∀ i, out (.site i) = final i := by
  let f := Frame.live (packed w start.pc.val) start.reg elapsed
  let decoded := Startup.decoded pub f H (packed w (limit.val-elapsed.val)) max suffix
  let mid := installStacks startup base decoded
  obtain ⟨t, ht, first⟩ := predecessor_run P lib last fits pub f H limit max suffix script base ready
  have hv : (packed w start.pc.val).val = start.pc.val := packed_val (lt_of_lt_of_le start.pc.isLt fits)
  have hl : TeamLocalClockPC.lookup p start.pc.val = .live start.pc := by
    simpa only [hv] using TeamLocalClockPC.lookup_packed start.pc fits
  simp only [f, Startup.result, Frame.elapsed, safe, ite_true, hl,
    afterStartup, Startup.remaining, hv, start.pc.isLt, and_self] at first
  have hmid := startup_site base pub start.pc (packed w start.pc.val) start.reg H
    (packed w (limit.val-elapsed.val)) elapsed max suffix
  have body := loop_segment P lib last run mid hmid
  let endBank := installStacks Port.site mid final
  have aux (i : Port r k (m*g)) (h : ∀ u, Port.site u ≠ i) : endBank i = mid i :=
    installStacks_outside mid final h
  have temp : endBank .tmp = [] := (aux _ (fun _ => by simp)).trans
    (installStacks_at startup_injective base decoded Startup.Port.tmp)
  have stream : endBank .outgoing = base .outgoing := (aux _ (fun _ => by simp)).trans
    (installStacks_outside base decoded (fun u => by cases u <;> simp [startup]))
  have empty : endBank .payload = [] := (aux _ (fun _ => by simp)).trans
    ((installStacks_outside base decoded (fun u => by cases u <;> simp [startup])).trans payload)
  have site (i : TeamSite.Port r k (m*g)) : endBank (.site i) = final i :=
    installStacks_at (fun _ _ h => Port.site.inj h) mid final i
  obtain ⟨time, hb, out, endRun, preserve⟩ := close_run P lib sg live last pub z.logged block' left'
    elapsed' max stamp rest endBank (fun i => (site (.clock i)).trans (finalClock i)) empty temp
  rw [stream] at endRun
  exact ⟨t+steps+time, by omega, out, (first.trans body).trans endRun, fun i => (preserve i).trans (site i)⟩

end TeamSite.Endpoint

end BorderVNP
end Computability
end OAI
