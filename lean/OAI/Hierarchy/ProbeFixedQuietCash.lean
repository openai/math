import OAI.Hierarchy.ProbeFixedQuietAttemptStock
import OAI.Hierarchy.ProtocolRAMCommittedPortLayout

namespace OAI
/-! # Exact cash preservation of the two idle modes in the paid native chart -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe StockCommit StripChart PurchaseStage RepairHistogram
open ThreeFlat.RAM
open scoped Classical BigOperators Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "st" => v.taskCommit P z width
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners
local notation "keys" => v.cashKeys P z width r banks src tab dst owners

/-- All genuine original candidate rows have a zero opening bit when the
observed mode is zero or one, independent of the frozen mark scan's answers. -/
theorem quiet_flags (a : Attempt) (entry : Memory W) (live : ready C (.attempt a) entry)
    (board : Board ((C).layout a) (repair C a) W) (wide : 4≤2^W)
    (mode : AttemptGate.actual (repair C a).policy (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))<2)
    (i : Fin ((C).layout a).candidates) : after C (.attempt a) entry ((repair C a).purchaseOut+i.val)=0 := by
  let B:=repair C a
  let L:=(C).layout a
  let m:=postSnapshot L B (prepared C a entry)
  let flag : Pass:=⟨B.purchaseOut,L.candidates,buyWord L B⟩
  have read:=attempt_read C a entry live board flag (List.mem_cons_of_mem _ (List.mem_cons_self ..)) i
  change after C (.attempt a) entry (B.purchaseOut+i.val)=(buyWord L B).eval m (i.val:Word W) at read
  rw [read]
  change (AttemptGate.ifMode B.policy 3 _ _).eval m (i.val:Word W)=0
  rw [AttemptGate.ifMode_eval _ _ _ _ _ _ wide (by decide)]
  change AttemptGate.actual B.policy m<2 at mode
  rw [ite_eq_right (by omega)]
  rfl

theorem quiet_paid (a : Attempt) (entry : Memory W) (scheduled : Event.attempt a∈events v.mesh)
    (live : ready C (.attempt a) entry) (positive : 0<width)
    (layout : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((v.privateArena P z width).base v.mesh (.attempt a)))
    (ports : PortPlan (st a) (b a) (input a entry) (f a).market.rows)
    (mode : AttemptGate.actual (repair C a).policy (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))<2) :
    let idx:=Succession v.mesh (.attempt a)
    ((A).read idx.2 (after C (.attempt a) entry)).paid=((A).read idx.1 entry).paid := by
  let t:=st a
  let u:=input a entry
  let B:=repair C a
  let out:=(t.native W (f a).market.rows (b a)).after u
  have entered:=v.entered P z width r banks src tab dst owners a entry live
  have off:=v.quiet_rows P z width r banks src tab dst owners a entry live layout mode
  have muted (e : Fin t.occurrences) :
      installedBits t.columns u e=0 ∧ consumedBits t.columns u e=0 :=
    ports.off e (by simpa only [StockCommit.liveRows,Finset.mem_filter,Finset.mem_univ,true_and] using off (ports.enum.symm e).1)
  have bc:=fresh_broadcastRoom _ _ _ layout.inputs layout.window.room
  have noTree (j : Fin (f a).market.rows) : out (t.broadcast+j.val)=0 :=
    (t.read_broadcast (b a) u j entered bc.fits ports.termRoom ports.copyRoom ports.sumRoom (bc.keeps j)).trans
      (ite_eq_right (off j))
  have noSpill (i : Fin t.goods) : out (t.plan.activeOut+t.goods+t.goods+i.val)=0 :=
    (v.quiet_receipt P z width r banks src tab dst owners a entry live layout ports mode i).2.2
  have noFlag (j : Fin (f a).market.rows) : out (B.purchaseOut+j.val)=0 :=
    v.quiet_flags P z width r banks src tab dst owners a entry live layout.board layout.window.wide mode j
  have bill:=t.buy_price (b a) u B.purchaseOut width (b a).copies positive entered
    (eventBoard _ _ _ layout.inputs layout.window.room) (keys a) (v.printedCharge P z width a)
    (fun _ _=>v.cost.atAttempt a) (v.coreCharge P z width a) (fun _=>v.openingCharge) muted noTree noSpill
  have cash:=v.posting P z width r banks src tab dst owners a entry scheduled live
  have zeros : (∑ j : Fin (f a).market.rows,(out (B.purchaseOut+j.val)).val*
        v.openingCharge (out ((keys a).buy j)).val)=0 :=
    Finset.sum_eq_zero (fun j _=>by rw [noFlag j];simp)
  let idx:=Succession v.mesh (.attempt a)
  have unchanged : ((A).read idx.2 out).paid=((A).read idx.1 entry).paid :=
    cash.trans ((congrArg (((A).read idx.1 entry).paid + ·) (bill.trans zeros)).trans (add_zero _))
  have finalMemory : out=after C (.attempt a) entry :=
    v.native_end P z width r banks src tab dst owners a entry
  exact (congrArg (fun last => ((A).read idx.2 last).paid) finalMemory).symm.trans unchanged

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
