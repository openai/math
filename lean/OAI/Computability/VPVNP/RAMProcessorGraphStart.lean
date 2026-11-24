import OAI.Computability.VPVNP.RAMProcessorGraphCredit

/-!
# Beginning a charged call in the site graph

The first call initializes the global allowance by subtraction. Every call
restores its own allowances, snapshots the start cost, and pays its startup
unit. Its private register bank and memory log are then reset before fetching
the first opcode of the fixed program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM

variable {w p r k : ℕ}

/-- Reset the call allowance, save the starting cost and charge for the new call. -/
def Snapshot.afterStart (s : Snapshot w p r k) (g : Word w) (hc : s.cost.val+1 < 2^w) :=
  s.setCredit s.publicFuel (s.publicH-1) (s.siteLeft-1) (Charges.prevWord g) ⟨s.cost.val+1,hc⟩
    (wordBits s.cost) (wordBits (0 : Word w))

/-- Instruction count of the call-start credit and reset routine. -/
def Snapshot.startTicks (s : Snapshot w p r k) :=
  CallCredit.resetTicks w s.publicH s.publicFuel s.fuel s.callLeft s.savedStart s.ordinal + (8*w+6)

theorem newCall_run (T : Template p r k) (s : Snapshot w p r k)
    (hH : 0 < s.publicH) (hs : 0 < s.siteLeft) (hg : 0 < s.globalLeft.val) (hc : s.cost.val+1 < 2^w) :
    StackRuns (table T) s.startTicks (atLabel T .newCall) s.bank (atLabel T .fresh)
      (s.afterStart s.globalLeft hc).bank := by
  apply credit_routine T s (rt := CallCredit.startCall) rfl
  exact CallCredit.startCall_run s.publicH s.publicFuel s.fuel s.callLeft s.siteLeft s.cap s.globalLeft s.cost s.savedStart s.ordinal hH hs hg hc

theorem newCall_reject (T : Template p r k) (s : Snapshot w p r k)
    (bad : s.publicH = 0 ∨ s.siteLeft = 0 ∨ s.globalLeft.val = 0 ∨ 2^w ≤ s.cost.val+1) :
    RejectRun (table T) (CallCredit.resetTicks w s.publicH s.publicFuel s.fuel s.callLeft s.savedStart s.ordinal +
      Charges.failureTicks s.publicH s.siteLeft s.globalLeft) (atLabel T .newCall) s.bank := by
  obtain ⟨_, run⟩ := CallCredit.startCall_reject s.publicH s.publicFuel s.fuel s.callLeft s.siteLeft
    s.cap s.globalLeft s.cost s.savedStart s.ordinal bad
  exact ProcessorFlow.routine_reject (blocks := blocks T) (l := .newCall) (next := .fresh)
    (fun _ _ h => Port.credit.inj h) (r := CallCredit.startCall) rfl run CallCredit.startCall_halt (fun _ => rfl)

theorem first_run (T : Template p r k) (s : Snapshot w p r k)
    (hH : 0 < s.publicH) (hs : 0 < s.siteLeft) (hlt : s.cost.val < s.cap.val) :
    StackRuns (table T) (16*w+7+s.startTicks) (atLabel T .first) s.bank (atLabel T .fresh)
      (s.afterStart (s.cap-s.cost) ((Nat.succ_le_of_lt hlt).trans_lt s.cap.isLt)).bank := by
  apply credit_routine T s (rt := CallCredit.firstCall) rfl
  exact CallCredit.firstCall_run s.publicH s.publicFuel s.fuel s.callLeft s.siteLeft s.cap s.globalLeft s.cost s.savedStart s.ordinal hH hs hlt

/-- Initialize private registers and the write log at the template's entry. -/
def Snapshot.afterFresh (s : Snapshot w p r k) (T : Template p r k) : Snapshot w p r k :=
  {s with cfg := ⟨T.entry, s.cfg.persistent, fun _ => 0, []⟩}

theorem fresh_run (T : Template p r k) (s : Snapshot w p r k) :
    ∃ t ≤ r*(8*w+3)+3*(s.cfg.writes.length*(w+1)+1)+2,
      StackRuns (table T) t (atLabel T .fresh) s.bank (atLabel T (.segment T.entry)) (s.afterFresh T).bank := by
  obtain ⟨t, ht, hr⟩ := ISA.freshCall_run s.pub s.cfg.persistent (fun i => wordBits (s.cfg.reg i))
    s.cfg.writes (by simp)
  refine ⟨t, ht, ProcessorFlow.run (blocks := blocks T) (l := .fresh) ?_⟩
  change ((Fragment.returning (ISA.freshCall (r := r) (k := k)) (Label.segment T.entry : Label p r)).onPorts Port.isa).Runs t s.bank _ (s.afterFresh T).bank
  apply Fragment.runs_framed (ports := Port.isa) (fun _ _ h => Port.isa.inj h)
    (Fragment.returning_runs hr (Label.segment T.entry : Label p r))
  · intro i
    cases i <;> rfl
  · intro i
    cases i <;> rfl
  · intro j hj
    cases j with
    | isa i => exact (hj i rfl).elim
    | test i => cases i with | word f => cases f <;> rfl | _ => rfl
    | record i => cases i <;> rfl
    | _ => rfl

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
