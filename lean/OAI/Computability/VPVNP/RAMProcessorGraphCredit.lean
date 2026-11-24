import OAI.Computability.VPVNP.RAMProcessorGraphRuns

/-!
# Charging transitions of the linked site graph

The transfer to a read or write payload is possible only after all three
allowances are checked. On a failing allowance the graph halts inside the
charging routine. The probe ordinal increases after the record emission.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM

variable {w p r k : ℕ}

/-- Update the runtime instruction, call, site and global credit registers. -/
def Snapshot.setCredit (s : Snapshot w p r k) (fuel callLeft siteLeft : ℕ) (g cost : Word w)
    (saved ordinal : List Bool) : Snapshot w p r k :=
  {s with
    fuel := fuel
    callLeft := callLeft
    siteLeft := siteLeft
    globalLeft := g
    cost := cost
    savedStart := saved
    ordinal := ordinal}

theorem Snapshot.credit_frame (s : Snapshot w p r k) (fuel callLeft siteLeft : ℕ) (g cost : Word w)
    (saved ordinal : List Bool) (j : Port r k) (hj : ∀ i, Port.credit i ≠ j) :
    (s.setCredit fuel callLeft siteLeft g cost saved ordinal).bank j = s.bank j := by
  cases j with
  | credit i => exact (hj i rfl).elim
  | test i => cases i with | word f => cases f <;> rfl | _ => rfl
  | record i => cases i with | field i => fin_cases i <;> rfl | _ => rfl
  | _ => rfl

theorem credit_routine (T : Template p r k) (s : Snapshot w p r k) {rt : FiniteRoutine CallCredit.Port}
    {l next : Label p r} (link : blocks T l = (Fragment.returning rt next).onPorts Port.credit)
    {t fuel callLeft siteLeft g cost saved ordinal}
    (h : rt.Runs t s.credit (s.setCredit fuel callLeft siteLeft g cost saved ordinal).credit) :
    StackRuns (table T) t (atLabel T l) s.bank (atLabel T next)
      (s.setCredit fuel callLeft siteLeft g cost saved ordinal).bank := by
  apply ProcessorFlow.run (blocks := blocks T)
  rw [link]
  exact Fragment.runs_framed (fun _ _ h => Port.credit.inj h) (Fragment.returning_runs h next)
    (fun _ => rfl) (fun _ => rfl) (fun j hj => s.credit_frame fuel callLeft siteLeft g cost saved ordinal j hj)

/-- The snapshot after a successful unit charge for a probe. -/
def Snapshot.afterCharge (s : Snapshot w p r k) (hc : s.cost.val+1 < 2^w) :=
  s.setCredit s.fuel (s.callLeft-1) (s.siteLeft-1) (Charges.prevWord s.globalLeft) ⟨s.cost.val+1,hc⟩
    s.savedStart s.ordinal

theorem precharge_run (T : Template p r k) (s : Snapshot w p r k) {l next : Label p r}
    (link : blocks T l = (Fragment.returning CallCredit.prepareProbe next).onPorts Port.credit)
    (hc : s.cost.val+1 < 2^w) (hg : 0 < s.globalLeft.val) (hcall : 0 < s.callLeft) (hsite : 0 < s.siteLeft) :
    StackRuns (table T) (8*w+6) (atLabel T l) s.bank (atLabel T next) (s.afterCharge hc).bank := by
  apply credit_routine T s link
  have h := CallCredit.prepareProbe_run s.publicH s.publicFuel s.fuel (s.callLeft-1) (s.siteLeft-1)
    s.cap s.globalLeft s.cost s.savedStart s.ordinal hg hc
  simpa only [Snapshot.setCredit, Snapshot.credit, Nat.sub_add_cancel hcall, Nat.sub_add_cancel hsite] using h

theorem precharge_reject (T : Template p r k) (s : Snapshot w p r k) {l next : Label p r}
    (link : blocks T l = (Fragment.returning CallCredit.prepareProbe next).onPorts Port.credit)
    (bad : s.callLeft = 0 ∨ s.siteLeft = 0 ∨ s.globalLeft.val = 0 ∨ 2^w ≤ s.cost.val+1) :
    RejectRun (table T) (Charges.failureTicks s.callLeft s.siteLeft s.globalLeft) (atLabel T l) s.bank := by
  obtain ⟨_, hr⟩ := CallCredit.prepareProbe_reject s.publicH s.publicFuel s.fuel s.callLeft s.siteLeft
    s.cap s.globalLeft s.cost s.savedStart s.ordinal bad
  exact ProcessorFlow.routine_reject (blocks := blocks T) (fun _ _ h => Port.credit.inj h)
    link hr CallCredit.prepareProbe_halt (fun _ => rfl)

/-- The snapshot after incrementing the emitted probe's ordinal. -/
def Snapshot.afterIncrement (s : Snapshot w p r k) (o : Word w) (ho : o.val+1 < 2^w) :=
  s.setCredit s.fuel s.callLeft s.siteLeft s.globalLeft s.cost s.savedStart (wordBits (⟨o.val+1,ho⟩ : Word w))

theorem increment_run (T : Template p r k) (s : Snapshot w p r k) (next : Fin p) (o : Word w)
    (hord : s.ordinal = wordBits o) (ho : o.val+1 < 2^w) :
    StackRuns (table T) (4*w+2) (atLabel T (.increment next)) s.bank (atLabel T (.segment next))
      (s.afterIncrement o ho).bank := by
  apply credit_routine T s (rt := CallCredit.finishProbe) rfl
  have hr := CallCredit.finishProbe_bank s.publicH s.publicFuel s.fuel s.callLeft s.siteLeft
    s.cap s.globalLeft s.cost o s.savedStart ho
  simpa only [Snapshot.credit, Snapshot.setCredit, hord] using hr

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
