import OAI.Computability.BorderVNP.TeamSiteTimedFrame
import OAI.Computability.BorderVNP.TeamSiteTimedBurst
import OAI.Computability.BorderVNP.TeamSiteTimedSupply
import OAI.Computability.BorderVNP.TeamSiteStop

/-! # Physical stopping cases for the trusted-clock team loop

An accepted or deferred instruction reaches its true endpoint without touching the
remaining supply. A rejected guard or bad range reaches a physical rejecting row
outside the sorter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP RAMTape BurstRAM TeamPrivateFragment TeamSiteEvents TeamSiteChoices SupplyRun
open RAMSerialization (WordRecord)

variable {Q Γ : Type} {w p r k a m g H : ℕ} {hw : 2 ≤ w+1}
variable (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (mark : Fin a → Γ)
local notation "FullBank" => Stacks (TeamClocked.Port (Layout.Port r k ((m+1)*g)))

/-- The physically reached label distinguishes a good live or halted close from
a rejected instruction, even when an earlier valid private return had weight zero. -/
def outcome (last : Bool) (sg : Option Bool) (pc : Fin p) (q : Label P Q m g) : Verdict → Prop
  | .accepted => q = loopLabel last (.close sg none)
  | .handoff => q = loopLabel last (.close sg (some pc))
  | .reject => (∃ z : Endpoint.Label P Q (m+1) g, q = .site (.block z)) ∧ code P lib mark q = .halt false

private theorem noncallback (pub : Fin k → Word w) (s : TeamOpcode.State w p r) (c : Window w)
    (last : Bool) (sg : Option Bool) (ex : TeamLocalClock.Loop.Exit p r a) (q : Loop.Label P Q (m+1) g)
    (guard : exit P pub s c = ex) (terminal : ∀ out, ex ≠ .callback out)
    (row : regular P lib mark (.clock sg (.exit ex)) = .goto q)
    (base : FullBank) (suffix : List Bool) (safe : c.Safe) (clock : base ∘ loopPort ∘ Port.clock = c.bank pub s) :
    ∃ t ≤ 1050*(w+1)^2+1, StackRuns (replay (code P lib mark)) t
      (loopLabel last (.clock sg (.enter s.pc)),suffix) base (loopLabel last q,suffix) base := by
  let b := base ∘ loopPort (m:=m) (g:=g)
  obtain ⟨t,ht,run⟩ := regular_clock P lib mark sg pub s c.block c.global c.elapsed c.cap safe b clock suffix
  change StackRuns (replay (regular P lib mark)) _ _ _ (.clock sg (.exit (exit P pub s c)),suffix)
    (installStacks Port.clock b (outputBank P pub s c)) at run
  rw [guard,noncallback_bank P pub s c (fun o => guard ▸ terminal o),
    installStacks_eq (fun _ _ he => Port.clock.inj he) b _ (congrFun clock)] at run
  have go : StackRuns (replay (regular P lib mark)) 1 (.clock sg (.exit ex),suffix) b (q,suffix) b :=
    replay_segment (.cons (.goto row) (.nil ..)) suffix
  have lift := regular_lift P lib mark last base (run.trans go)
  rw [installStacks_eq loopPort_injective base b (fun _ => rfl)] at lift
  exact ⟨t+1,by omega,lift⟩

private theorem bad_callback (last : Bool) (sg : Option Bool) (pc : Fin p) (bank : PrivateRAM.LogConfig w p r)
    (out : TeamOpcode.Exit p r a) (bad : Invalid bank out) (win : Window w) (tick : Word w)
    (pub : Fin k → Word w) (rs : List (WordRecord (w+1))) (base : FullBank)
    (ready : Work.Ready hw H rs (base ∘ loopPort)) (clock : base ∘ loopPort ∘ Port.clock = win.callbackBank pub bank.reg tick)
    (suffix : List Bool) :
    ∃ t q b, t ≤ 1+TeamBurstCallback.rejectCost w ∧ StackRuns (replay (code P lib mark)) t
      (loopLabel last (.clock sg (.exit (.callback out))),suffix) base (q,suffix) b ∧ outcome P lib mark last sg pc q .reject := by
  cases bad with
  | nativeReject | nativeReturn =>
    exact ⟨2,.site (.block .invalid),base,by unfold TeamBurstCallback.rejectCost; omega,
      .cons (.goto rfl) (.cons (.goto rfl) (.nil ..)),⟨.invalid,rfl⟩,rfl⟩
  | badAddress j addr len next overflow =>
    obtain ⟨t,ht,b,run,halt⟩ := burst_reject P lib mark last sg j addr len next ready
      (bank.reg addr) (bank.reg len) tick win.cap (congrFun clock (.isa (.reg addr)))
      (congrFun clock (.isa (.reg len))) (congrFun clock .stamp) (congrFun clock .maxBurst)
      (fun h => Nat.not_le_of_lt overflow h.2) suffix
    exact ⟨t,_,b,ht,run,⟨_,rfl⟩,halt⟩

/-- The finite native supply description's terminal case always gives a real physical
terminal or the precise handoff label. The accepting and deferred cases preserve the
full caller bank. -/
theorem stop_run (pub : Fin k → Word w) (N : ℕ) (s : TeamOpcode.State w p r) (c : Window w)
    (u : Supply) (v : Verdict) (halt : SupplyRun.Run P pub (fun j => TimedSupply.shadow N (lib j)) (N+1) s c u [] s c v)
    (last : Bool) (sg : Option Bool) (rs : List (WordRecord (w+1))) (base : FullBank) (suffix : List Bool)
    (safe : c.Safe) (clock : base ∘ loopPort ∘ Port.clock = c.bank pub s) (ready : Work.Ready hw H rs (base ∘ loopPort)) :
    ∃ t q b, t ≤ Work.closeBudget w ∧ StackRuns (replay (code P lib mark)) t
      (loopLabel last (.clock sg (.enter s.pc)),suffix) base (q,suffix) b ∧
      outcome P lib mark last sg s.pc q v ∧ (v ≠ .reject → b = base) := by
  cases halt with
  | accept h =>
    obtain ⟨t,ht,run⟩ := noncallback P lib mark pub s c last sg _ (.close sg none) h (fun _ => by simp) rfl base suffix safe clock
    exact ⟨t,_,base,by unfold Work.closeBudget; omega,run,rfl,fun _ => rfl⟩
  | handoff h =>
    obtain ⟨t,ht,run⟩ := noncallback P lib mark pub s c last sg _ (.close sg (some s.pc)) h (fun _ => by simp) rfl base suffix safe clock
    exact ⟨t,_,base,by unfold Work.closeBudget; omega,run,rfl,fun _ => rfl⟩
  | rejectGuard h =>
    obtain ⟨t,ht,run⟩ := noncallback P lib mark pub s c last sg _ .reject h (fun _ => by simp) rfl base suffix safe clock
    have endStep : StackRuns (replay (code P lib mark)) 1 (loopLabel last .reject,suffix) base
        (.site (.block .invalid),suffix) base := .cons (.goto rfl) (.nil ..)
    exact ⟨t+1,_,base,by unfold Work.closeBudget TeamBurstCallback.rejectCost; omega,
      run.trans endStep,⟨⟨.invalid,rfl⟩,rfl⟩,fun _ => rfl⟩
  | rejectCallback admit _ reason =>
    let b := base ∘ loopPort (m:=m) (g:=g)
    let win := c.charge (opcodeBurst P s).val
    let cb := win.callbackBank pub (TeamOpcode.prepare P pub s).2.reg c.first
    let mid := installStacks Port.clock b cb
    obtain ⟨t,ht,guard⟩ := regular_clock P lib mark sg pub s c.block c.global c.elapsed c.cap safe b clock suffix
    change StackRuns (replay (regular P lib mark)) _ _ _ (.clock sg (.exit (exit P pub s c)),suffix)
      (installStacks Port.clock b (outputBank P pub s c)) at guard
    rw [admit,callback_bank P pub s c _ admit] at guard
    have lift := regular_lift P lib mark last base guard
    let full := installStacks loopPort base mid
    have back : full ∘ loopPort = mid := loop_install base mid
    have hb : (full ∘ loopPort) ∘ Port.clock = cb := by
      rw [back]; exact funext fun j => installStacks_at (fun _ _ he => Port.clock.inj he) ..
    have wr : Work.Ready hw H rs (full ∘ loopPort) := back ▸ ready.installClock cb
    obtain ⟨z,q,out,hz,path,reject⟩ := bad_callback P lib mark last sg s.pc _ _ reason win c.first pub rs full wr hb suffix
    exact ⟨t+z,q,out,by unfold Work.closeBudget; omega,lift.trans path,reject,fun h => (h rfl).elim⟩

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
