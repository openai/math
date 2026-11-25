import OAI.Hierarchy.ProbeCommittedMaskLive
import OAI.Hierarchy.ProtocolRAMNativeMaskSpace
import OAI.Hierarchy.ProtocolRAMStockStageFrame

namespace OAI
/-! # Native live-strip test for a debit occurring after the labels and stock seed -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage RepairHistogram StockCommit
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k q goods : ℕ}
local notation "W" => wordBits z d copies

/-- Only the original mask word is read back from the input consumed by the priced
commit. Every native verification, verdict, label and stock write is accounted for. -/
theorem Market.committed_live_at_price (v : Market z d k) (B : Repair q goods) (base : Shelf.Mem z d)
    (j : Fin v.rows) (a : Area) (s : Sources) (g : LabelSource) (ready : v.ready base)
    (owner : B.batch.owner=.row) (installed : B.failedMIS=v.failures.bank) (fits : v.rows≤2^W)
    (rows : v.rows≤v.failures.rows) (cap : v.rows≤v.failures.bank.size) (bits : v.rows≤B.repairBits.size)
    (wide : 4≤2^W) (cut : v.failures.cut<2^W)
    (prior : v.failures.base+v.rows≤B.tests.excess.out ∧ v.failures.base+v.rows≤B.tests.payload.out ∧
      v.failures.base+v.rows≤B.tests.discrepancy.out) (mask : MaskSpace v.layout B)
    (audit : AuditReady (audits v.layout B) (postSnapshot v.layout B (v.prefix.after base)))
    (low : B.repairBits.base+v.rows≤g.out) (ordered : g.out≤a.start)
    (charged : j∈liveRows (enabledBatch v.layout B) (stageInput a s g (postOutput v.layout B (v.prefix.after base))) v.rows) :
    v.failures.live.eval base (j.val:Word W)≠0 := by
  apply v.live_of_mask B base ready j owner installed fits rows cap bits wide cut prior
  have read := (Finset.mem_filter.mp charged).2.1.1
  change B.repairBits.read (stageInput a s g (postOutput v.layout B (v.prefix.after base))) (j.val:Word W)≠0 at read
  rw [Bank.read,Fin.val_cast_of_lt (j.isLt.trans_le fits),Nat.mod_eq_of_lt (j.isLt.trans_le bits),
    stage_frame a s g _ _ ((Nat.add_lt_add_left j.isLt _).trans_le low) ordered] at read
  change image B.verdict 1 _ (auditOut _ (postSnapshot v.layout B (v.prefix.after base))) (B.repairBits.base+j.val)≠0 at read
  rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (mask.verdict j)),audit_below _ _ audit _ (mask.audit j)] at read
  exact read

/-- Fixed pointer and count inequalities at one physical position. The table
readiness and audit inputs are established by the actual chronological execution. -/
structure Market.MaskBounds (v : Market z d k) (B : Repair q goods) (a : Area) (g : LabelSource) : Prop where
  rows : v.rows≤v.failures.rows
  cap : v.rows≤v.failures.bank.size
  bits : v.rows≤B.repairBits.size
  cut : v.failures.cut<2^W
  prior : v.failures.base+v.rows≤B.tests.excess.out ∧ v.failures.base+v.rows≤B.tests.payload.out ∧
    v.failures.base+v.rows≤B.tests.discrepancy.out
  mask : MaskSpace v.layout B
  low : B.repairBits.base+v.rows≤g.out
  ordered : g.out≤a.start

/-- The native scalar address obligations shared by both kinds of strip. -/
structure Market.DateMaskRoom (v : Market z d k) (B : Repair q goods) (base : Shelf.Mem z d) (a : Area) (g : LabelSource) : Prop where
  ready : v.ready base
  owner : B.batch.owner=.row
  installed : B.failedMIS=v.failures.bank
  fits : v.rows≤2^W
  rows : v.rows≤v.failures.rows
  cap : v.rows≤v.failures.bank.size
  bits : v.rows≤B.repairBits.size
  wide : 4≤2^W
  cut : v.failures.cut<2^W
  prior : v.failures.base+v.rows≤B.tests.excess.out ∧ v.failures.base+v.rows≤B.tests.payload.out ∧
    v.failures.base+v.rows≤B.tests.discrepancy.out
  mask : MaskSpace v.layout B
  audit : AuditReady (audits v.layout B) (postSnapshot v.layout B (v.prefix.after base))
  low : B.repairBits.base+v.rows≤g.out
  ordered : g.out≤a.start

theorem Market.MaskBounds.at_ready {v : Market z d k} {C : Chart W q goods} {e : Attempt}
    {area : Area} {g : LabelSource} (limits : v.MaskBounds (repair C e) area g) (before : Memory W)
    (native : Calendar.ready C (.attempt e) before)
    («prefix» : C.frozen e=v.prefix) (layout : C.layout e=v.layout)
    (owner : (repair C e).batch.owner=.row) (installed : (repair C e).failedMIS=v.failures.bank)
    (fit : v.rows≤2^W) : v.DateMaskRoom (repair C e) ((guard C e).apply before) area g := by
  have ready:=native.2.1
  rw [«prefix»] at ready
  have tested:=native.2.2.2.2.2.2.1
  rw [prepared,«prefix»,layout] at tested
  have wide : 4≤2^W:=Nat.le_trans (by decide : 4≤2^2)
    (Nat.pow_le_pow_right (by decide) (by unfold Native.wordBits;omega))
  exact ⟨ready,owner,installed,fit,limits.rows,limits.cap,limits.bits,wide,limits.cut,
    limits.prior,limits.mask,tested,limits.low,limits.ordered⟩

theorem Market.DateMaskRoom.live {v : Market z d k} {B : Repair q goods} {base : Shelf.Mem z d} {a : Area} {g : LabelSource}
    (r : v.DateMaskRoom B base a g) (s : Sources) (j : Fin v.rows)
    (charged : j∈liveRows (enabledBatch v.layout B) (stageInput a s g (postOutput v.layout B (v.prefix.after base))) v.rows) :
    v.failures.live.eval base (j.val:Word W)≠0 :=
  v.committed_live_at_price B base j a s g r.ready r.owner r.installed r.fits r.rows r.cap r.bits r.wide r.cut r.prior
    r.mask r.audit r.low r.ordered charged

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
