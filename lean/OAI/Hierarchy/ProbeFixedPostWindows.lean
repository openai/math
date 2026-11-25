import OAI.Hierarchy.ProbeFixedCatalystMask
import OAI.Hierarchy.ProbeFixedStockOperands
import OAI.Hierarchy.ProtocolRAMCalendarTally
import OAI.Hierarchy.ProtocolRAMCalendarStripSeen

namespace OAI
/-! # Physical address and count bounds for native postprocessing on a scheduled date -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe StripChart PurchaseStage
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
local notation "C" => v.nativeChart P z width r banks src tbl dst owners
local notation "f" => v.nativeFormats P z width
local notation "A" => v.privateArena P z width
local notation "W" => wordBits z (2^v.W) copies
local notation "q₀" => (catalogue F (v.configured (v.seed P z width)) v.cost).alphabet

theorem post_window (a : Attempt) (scheduled : Event.attempt a∈events v.mesh)
    (fits : (A).endAddress v.mesh<2^W) :
    (f a).board.keys<2^W ∧ (f a).board.verdict+1<2^W := by
  have endEvent := (v.attempt_room P z width a).trans_lt (((A).within v.mesh _ scheduled).trans_lt fits)
  have inside : (f a).board.verdict+1≤(f a).pricedArea.stop := Slab.verdict_before (f a)
  have limit := inside.trans_lt endEvent
  exact ⟨(v.stock_keys P z width a).2.trans_lt limit,limit⟩

theorem post_policy_words (a : Attempt) (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W) :
    let B:=repair C a
    B.policy.stop.base+B.policy.stop.size≤B.keys ∧ B.policy.excess.base+B.policy.excess.size≤B.keys ∧
    B.policy.payload.base+B.policy.payload.size≤B.keys ∧ B.policy.discrepancy.base+B.policy.discrepancy.size≤B.keys := by
  intro B
  have mask:=(v.catalystMaskBounds P z width r banks src tbl dst owners a threshold).mask
  have low : B.repairBits.base≤B.keys := Nat.le_add_right ..
  have cell (b : Bank) (before : b.base<B.repairBits.base) (size : b.size=1) : b.base+b.size≤B.keys := by
    rw [size]
    exact before.trans_le low
  exact ⟨cell _ mask.stop rfl,cell _ mask.excess rfl,cell _ mask.payload rfl,cell _ mask.discrepancy rfl⟩

private theorem shelf_before_mask {h radix lanes letters goods : ℕ} (ff : Format h radix lanes letters goods) :
    ff.market.shelf.firstBase ≤ ff.maskStart := by
  have first : ff.market.shelf.firstBase ≤ ff.testsStart := by
    unfold Format.testsStart Market.flags PurchaseFrozen.Shelf.flagsBase
    omega
  apply first.trans
  unfold Format.maskStart PostLayout.afterTests
  omega

private theorem repair_mask_inputs {letters goods : ℕ} (B : Repair letters goods)
    (stop : B.policy.stop.base+B.policy.stop.size≤B.repairBits.base)
    (excess : B.policy.excess.base+B.policy.excess.size≤B.repairBits.base)
    (payload : B.policy.payload.base+B.policy.payload.size≤B.repairBits.base)
    (disc : B.policy.discrepancy.base+B.policy.discrepancy.size≤B.repairBits.base)
    (owner : B.batch.owner=.row) (mis : B.failedMIS.base+B.failedMIS.size≤B.repairBits.base) :
    (repairMask B).inputEnd≤B.repairBits.base := by
  have mode : (AttemptGate.mode B.policy).inputEnd≤B.repairBits.base := by
    cases ex : B.policy.reserve <;> cases ey : B.policy.injection <;>
      simp only [AttemptGate.mode,ex,ey,Bool.false_eq_true,ite_true,ite_false,AttemptGate.nonzero,Expr.inputEnd,
        max_le_iff,Nat.zero_le,and_true,stop,excess,payload,disc]
  simp only [repairMask,AttemptGate.ifRepair,AttemptGate.ifMode,owner,Expr.inputEnd,max_le_iff,Nat.zero_le,
    mode,mis,and_true]

set_option cleanup.letToHave false in
set_option maxHeartbeats 1000000 in
/-- A candidate reads its originally computed failed-strip bit and the four single-word
phase flags. Every such source is already present before the repair mask is written. -/
theorem post_mask (a : Attempt) (scheduled : Event.attempt a∈events v.mesh)
    (fits : (A).endAddress v.mesh<2^W) (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W) :
    let B:=repair C a
    (repairMask B).Fits W B.repairBits.base ∧ B.repairBits.base+((C).layout a).candidates<2^W := by
  intro B
  let ff:=f a
  let sized:=v.sized (v.seed P z width) width
  let slab:=v.slab (v.seed P z width) P width
  let base:=(A).base v.mesh (.attempt a)
  have hb:=v.catalystMaskBounds P z width r banks src tbl dst owners a threshold
  have layout : B.failedMIS.base=base+Slab.selectorSpan sized ∧ B.failedMIS.size=Slab.failureSpan sized ∧
      ff.market.shelf.firstBase=Slab.first slab sized base := by
    cases a <;> exact ⟨rfl,rfl,rfl⟩
  have before : B.failedMIS.base+B.failedMIS.size≤ff.market.shelf.firstBase := by
    rw [layout.1,layout.2.1,layout.2.2]
    exact Nat.le_add_right ..
  have mis : B.failedMIS.base+B.failedMIS.size≤B.repairBits.base := before.trans (shelf_before_mask ff)
  have cell (b : Bank) (small : b.base<B.repairBits.base) (one : b.size=1) : b.base+b.size≤B.repairBits.base := by
    rw [one]
    exact small
  have hstop:=cell _ hb.mask.stop rfl
  have hex:=cell _ hb.mask.excess rfl
  have hp:=cell _ hb.mask.payload rfl
  have hd:=cell _ hb.mask.discrepancy rfl
  have owner : B.batch.owner=.row := by cases a <;> rfl
  have read := repair_mask_inputs B hstop hex hp hd owner mis
  have bounds:=v.post_window P z width a scheduled fits
  have capped : B.repairBits.base+((C).layout a).candidates≤ff.board.keys :=
    Nat.add_le_add_left hb.bits _
  have limit:=capped.trans_lt bounds.1
  exact ⟨Expr.fits_of_inputEnd _ read ((Nat.le_add_right _ _).trans_lt limit),limit⟩

/-- Width and the fixed menu alphabet bound every potential private counter,
including those on dates on which the logical repair is disabled. -/
theorem post_counts (a : Attempt) (payload : width<2^W) (alphabet : v.menu.alphabet≤2^W)
    (total : v.menu.alphabet*width<2^W) :
    q₀≤2^W ∧ (repair C a).batch.copies<2^W ∧ q₀*(repair C a).batch.copies<2^W := by
  have size : q₀=v.menu.alphabet := (v.catalogue_words (v.seed P z width) width).1
  have occurrence : (repair C a).batch.copies=(f a).histMass := by cases a <;> rfl
  have small : (repair C a).batch.copies≤width := by
    rw [occurrence,(v.ordinary_dimensions P z width a).2]
    exact Nat.div_le_self ..
  exact ⟨size.le.trans alphabet,small.trans_lt payload,(Nat.mul_le_mul size.le small).trans_lt total⟩

private theorem priced_replaced {h d kk alphabet goods rows edges : ℕ}
    (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format h d kk alphabet goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink rows edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (a : Attempt) :
    let calendar := pricedInstalled c finish prices format feeds sink idBase role ids
    PostLayout.place (calendar.layout a) (repair calendar a) (format a).maskStart (format a).indexBits =
      repair calendar a := by
  intro calendar
  rfl

/-- Replacing addresses of an already placed register program with the canonical ones
recovers that exact program, including the scheduled reserve/injection branch flags. -/
theorem post_replaced (a : Attempt) :
    PostLayout.place ((C).layout a) (repair C a) (f a).maskStart (f a).indexBits=repair C a := by
  dsimp only [nativeChart,StripChart.chart,nativeFormats]
  exact priced_replaced _ _ _ _ _ _ _ _ _ a

/-- The original calendar's physical register validator and all column checks can be
evaluated on every raw input tape, whether the private count words pass or fail. -/
theorem post_audit_of_reads (a : Attempt) (scheduled : Event.attempt a∈events v.mesh)
    (fits : (A).endAddress v.mesh<2^W) (payload : width<2^W) (alphabet : v.menu.alphabet≤2^W)
    (total : v.menu.alphabet*width<2^W)
    (reads : SnapshotReads ((C).layout a) (repair C a) (f a).board.keys) :
    let L:=(C).layout a
    let B:=repair C a
    Board L B W ∧ (∀m : Memory W,AuditReady (audits L B) m) ∧ OrderedTallies (audits L B) ∧
      (verdict (audits L B)).Fits W B.verdict := by
  intro L B
  have hw:=v.post_window P z width a scheduled fits
  have sizes:=v.post_counts P z width r banks src tbl dst owners a payload alphabet total
  have same:=v.post_replaced P z width r banks src tbl dst owners a
  let g:=f a
  have bound : SnapshotReads L (PostLayout.place L B g.maskStart g.indexBits) (g.maskStart+2^g.indexBits) := by
    rw [show PostLayout.place L B g.maskStart g.indexBits=B from same]
    exact reads
  have endWord : (PostLayout.place L B g.maskStart g.indexBits).verdict+1<2^W := by
    rw [show PostLayout.place L B g.maskStart g.indexBits=B from same]
    exact hw.2
  have native:=placed_board L B g.maskStart g.indexBits W bound hw.1
  have audit:=placed_audit L B g.maskStart g.indexBits bound endWord sizes.1 sizes.2.1 sizes.2.2
  have rep : PostLayout.place L B g.maskStart g.indexBits=B := same
  rw [rep] at native audit
  exact ⟨native,audit⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
