import OAI.Computability.BorderVNP.TeamSiteChunkRun
import OAI.Computability.BorderVNP.TeamSiteSupplyBank
import OAI.Computability.BorderVNP.TeamSiteSupplyChunk

/-! # Exact physical outcomes of a stopped processor instruction loop

The clock guard preserves the bank on a live handoff or an accepted halt. An
admitted but out-of-range read interval stops at the range check's rejecting
label before any old-word guess. These failures remain distinguishable from
a valid chunk of signed weight zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.SupplyRun

open VPVNP RAMTape TeamPrivateFragment TeamSiteChoices
open BurstRAM (Word wordBits)
open TeamRAM (Event)
open RAMSerialization (WordRecord)

variable {Q Γ : Type} {w p r k a m g H : ℕ} {hw : 2 ≤ w+1}

/-- A genuine local close, or an invalid halt outside all local close labels. -/
def Outcome (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (sg : Option Bool)
    (pc : Fin p) (label : Loop.Label P Q m g) : Verdict → Prop
  | .accepted => label = .close sg none
  | .handoff => label = .close sg (some pc)
  | .reject => Loop.code P lib label = .halt false ∧ ∀ z live, label ≠ .close z live

private theorem noncallback_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (pub : Fin k → Word w) (s : TeamOpcode.State w p r) (c : Window w) (sg : Option Bool)
    (ex : TeamLocalClock.Loop.Exit p r a) (q : Loop.Label P Q m g)
    (guard : exit P pub s c = ex) (terminal : ∀ out, ex ≠ .callback out)
    (row : Loop.code P lib (.clock sg (.exit ex)) = .goto q) (base : Stacks (Port r k (m*g))) (suffix : List Bool)
    (safe : c.Safe) (clock : base ∘ Port.clock = c.bank pub s) :
    ∃ n ≤ Work.closeBudget w, StackRuns (replay (Loop.code P lib)) n
      (.clock sg (.enter s.pc),suffix) base (q,suffix) base := by
  obtain ⟨t,ht,run⟩ := Loop.clock_run P lib sg pub s c.block c.global c.elapsed c.cap safe base clock suffix
  change StackRuns (replay (Loop.code P lib)) _ _ _ (.clock sg (.exit (exit P pub s c)),suffix) (installStacks Port.clock base (outputBank P pub s c)) at run
  rw [guard, noncallback_bank P pub s c (fun o => guard ▸ terminal o),
    installStacks_eq (fun _ _ he => Port.clock.inj he) base _ (congrFun clock)] at run
  have go : StackRuns (replay (Loop.code P lib)) 1 (.clock sg (.exit ex),suffix) base (q,suffix) base :=
    replay_segment (.cons (.goto row) (.nil ..)) suffix
  exact ⟨t+1,by unfold Work.closeBudget; omega,run.trans go⟩

private theorem invalid_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (sg : Option Bool) (pc : Fin p) (bank : BurstRAM.PrivateRAM.LogConfig w p r)
    (out : TeamOpcode.Exit p r a) (bad : Invalid bank out) (win : Window w) (tick : Word w)
    (pub : Fin k → Word w) (rs : List (WordRecord (w+1))) (base : Stacks (Port r k (m*g)))
    (ready : Work.Ready hw H rs base) (clock : base ∘ Port.clock = win.callbackBank pub bank.reg tick)
    (suffix : List Bool) :
    ∃ t q b, t ≤ 1+TeamBurstCallback.rejectCost w ∧
      StackRuns (replay (Loop.code P lib)) t (.clock sg (.exit (.callback out)),suffix) base (q,suffix) b ∧
      Outcome P lib sg pc q .reject := by
  cases bad with
  | nativeReject | nativeReturn =>
    exact ⟨1,.reject,base,Nat.le_add_right ..,.cons (.goto rfl) (.nil ..),rfl,fun _ _ => by simp⟩
  | badAddress j addr len next overflow =>
    obtain ⟨t,ht,b,run,halt⟩ := Work.reject_burst_label P lib sg j addr len next ready
      (bank.reg addr) (bank.reg len) tick win.cap (congrFun clock (.isa (.reg addr)))
      (congrFun clock (.isa (.reg len))) (congrFun clock .stamp) (congrFun clock .maxBurst)
      (fun h => Nat.not_le_of_lt overflow h.2) suffix
    exact ⟨t,_,b,ht,run,halt,fun _ _ => by simp⟩

/-- Every stopping case of the source loop has its exact physical path on the unchanged
remaining choice stream. Successful terminal cases leave all machine data intact. -/
theorem stop_run (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) (s : TeamOpcode.State w p r) (c : Window w)
    (supply : Supply) (v : Verdict) (halt : Run P pub lib fuel s c supply [] s c v)
    (sg : Option Bool) (rs : List (WordRecord (w+1))) (base : Stacks (Port r k (m*g))) (suffix : List Bool)
    (safe : c.Safe) (clock : base ∘ Port.clock = c.bank pub s) (ready : Work.Ready hw H rs base) :
    ∃ t q b, t ≤ Work.closeBudget w ∧
      StackRuns (replay (Loop.code P lib)) t (.clock sg (.enter s.pc),suffix) base (q,suffix) b ∧
      Outcome P lib sg s.pc q v ∧ (v ≠ .reject → b = base) := by
  cases halt with
  | accept h =>
    obtain ⟨t,ht,run⟩ := noncallback_run P lib pub s c sg _ (.close sg none) h (fun _ => by simp) rfl base suffix safe clock
    exact ⟨t,_,base,ht,run,rfl,fun _ => rfl⟩
  | handoff h =>
    obtain ⟨t,ht,run⟩ := noncallback_run P lib pub s c sg _ (.close sg (some s.pc)) h (fun _ => by simp) rfl base suffix safe clock
    exact ⟨t,_,base,ht,run,rfl,fun _ => rfl⟩
  | rejectGuard h =>
    obtain ⟨t,ht,run⟩ := noncallback_run P lib pub s c sg _ .reject h (fun _ => by simp) rfl base suffix safe clock
    exact ⟨t,_,base,ht,run,⟨rfl,fun _ _ => by simp⟩,fun _ => rfl⟩
  | rejectCallback admit _ reason =>
    let win := c.charge (opcodeBurst P s).val
    let cb := win.callbackBank pub (TeamOpcode.prepare P pub s).2.reg c.first
    let mid := installStacks Port.clock base cb
    obtain ⟨t,ht,guard⟩ := Loop.clock_run P lib sg pub s c.block c.global c.elapsed c.cap safe base clock suffix
    change StackRuns (replay (Loop.code P lib)) _ _ _ (.clock sg (.exit (exit P pub s c)),suffix) (installStacks Port.clock base (outputBank P pub s c)) at guard
    rw [admit, callback_bank P pub s c _ admit] at guard
    have hb : mid ∘ Port.clock = cb := funext fun j => installStacks_at (fun _ _ he => Port.clock.inj he) ..
    obtain ⟨u,q,b,hu,run,failed⟩ := invalid_run P lib sg s.pc _ _ reason win c.first pub rs mid (ready.installClock cb) hb suffix
    exact ⟨t+u,q,b,by unfold Work.closeBudget; omega,guard.trans run,failed,fun h => (h rfl).elim⟩

/-- Every complete source execution, including any rejected one, consumes its precise
choice spelling in the actual site loop. A successful closure retains the full record
and clock output for the physical outgoing frame and sorting tests. -/
theorem Run.replay (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) {s last : TeamOpcode.State w p r} {c fin : Window w}
    {supply : Supply} {es : List (Event w)} {v : Verdict} (run : Run P pub lib fuel s c supply es last fin v)
    (sg : Option Bool) (rs : List (WordRecord (w+1))) (base : Stacks (Port r k (m*g))) (suffix : List Bool)
    (safe : c.Safe) (clock : base ∘ Port.clock = c.bank pub s) (ready : Work.Ready hw H rs base)
    (space : rs.length+2*c.block.val ≤ 4*H) :
    ∃ t q b, t ≤ Work.chunkBudget w m g fuel es + Work.closeBudget w ∧
      StackRuns (TeamPrivateFragment.replay (Loop.code P lib)) t (.clock sg (.enter s.pc),chunkBits es++suffix) base (q,suffix) b ∧
      Outcome P lib (chunkSign sg es) last.pc q v ∧ (v ≠ .reject →
        Work.Ready hw H (rs++chunkSlots (c.elapsed.val+1) es) b ∧ b ∘ Port.clock = fin.bank pub last) := by
  have ch := run.chunk
  obtain ⟨n,mid,hn,body,hwork,hclock,_⟩ := ch.run P lib fuel pub sg rs base suffix safe clock ready space
  obtain ⟨t,q,b,ht,stop,ok,steady⟩ := stop_run P pub lib fuel last fin _ v run.stopped (chunkSign sg es)
    _ mid suffix (ch.clock safe).2.2.1 hclock hwork
  exact ⟨n+t,q,b,Nat.add_le_add hn ht,body.trans stop,ok,fun h => steady h ▸ ⟨hwork,hclock⟩⟩

end TeamSite.SupplyRun

end BorderVNP
end Computability
end OAI
