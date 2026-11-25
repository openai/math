import OAI.Hierarchy.ProtocolRAMCalendarElection
import OAI.Hierarchy.ProtocolRAMCalendarElectionGuard
import OAI.Hierarchy.ProtocolRAMCalendarStripPrivate
import OAI.Hierarchy.TaggedWireCalendarShelf
import OAI.Hierarchy.ProtocolRAMPurchaseMarketBelow

namespace OAI
/-! # Election on the actual chronological strip layout -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseStage PurchaseFrozen
open StripDirectory WireTelescope
open scoped Classical Fin.CommRing
variable {z d k q depth r : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "W" => wordBits z d copies
variable (v : Slab) (s : Boards z d k q depth) (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (c : Mesh) (initial width cap : ℕ) (finish : ℝ) (prices : PhasePrice) (catalogue : CatalogueRows.Board)
  (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
local notation "A" => arena v s
local notation "B" => install v s c
local notation "C" => chart F c A initial width cap B finish prices catalogue r banks src tbl dst owners
local notation "profiles" => formats F c A initial B

theorem mode_earlier (a b : Attempt)
    (prior : position c (.attempt b)<position c (.attempt a)) :
    (C).modeAt b<(A).base c (.attempt a) := by
  let p:=profiles b
  have cols : 2≤PostLayout.columnsCount p.checkedBoard := by unfold PostLayout.columnsCount;omega
  have mode : p.board.modeOut≤p.board.verdict :=
    Nat.add_le_add_left (Nat.mul_le_mul_right p.market.rows cols) _
  exact (mode.trans_lt (verdict_before p)).trans_le
    ((fit v s F c initial b).trans ((A).apart c prior))

/-- All earlier stocks, CT rows and price directories are identical in the
two native snapshots, even though their current private histograms differ. -/
theorem before_snapshot (a : Attempt) (left right : Memory W)
    (same : Below ((A).base c (.attempt a)) left right)
    (hl : ready C (.attempt a) left) (hr : ready C (.attempt a) right) :
    Below ((A).base c (.attempt a)) (HistogramShelf.snapshot C a left) (HistogramShelf.snapshot C a right) := by
  intro x hx
  have safe:=selector_protected (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners a x
    (hx.trans_le (Nat.le_add_right ..))
  exact (HistogramShelf.snapshot_frame C a left x hl safe.1).trans
    ((same x hx).trans (HistogramShelf.snapshot_frame C a right x hr safe.1).symm)

/-- The actual repair bitmap requires only the previous price-bearing stock
and the actual archived path coordinates. All chronological reads which follow
the current private page are evaluated by the real program. -/
theorem before_mask (a : Attempt) (left right : Memory W)
    (same : Below ((A).base c (.attempt a)) left right)
    (hl : ready C (.attempt a) left) (hr : ready C (.attempt a) right)
    (w4 : 4≤2^W)
    (excess : (repair C a).tests.excess.term.Fits W ((A).base c (.attempt a)))
    (payload : (repair C a).tests.payload.term.Fits W ((A).base c (.attempt a)))
    (failure : (profiles a).market.failures.effective.Fits W ((A).base c (.attempt a)))
    (threshold : (profiles a).market.failures.cut<2^W)
    (i : Fin ((C).layout a).candidates) :
    (repair C a).repairBits.read (HistogramShelf.snapshot C a left) (i.val:Word W)=
    (repair C a).repairBits.read (HistogramShelf.snapshot C a right) (i.val:Word W) := by
  let p:=profiles a
  let market:=p.atTime c finish prices a
  let t:=repair C a
  let base:=(A).base c (.attempt a)
  have pars:=sizes v s F c initial a
  have entered : base≤ market.prefix.start := by
    change _≤ min p.market.failures.base p.market.shelf.firstBase
    rw [pars.2.1,pars.2.2.2.1]
    exact le_min (Nat.le_add_right ..)
      (((Nat.le_add_right base (selectorSpan s)).trans (Nat.le_add_right _ (failureSpan s))).trans
        (Nat.le_add_right _ (2^(z+v.thresholdExtra))))
  have n : p.market.rows=rows s:=pars.1
  have low := market.shelf.first_le_flags market.sampler z d k market.depth
  have source := hl.2.1.2.1
  have endLow : market.failures.base+market.rows≤ market.flags :=
    (show market.failures.base+market.rows≤ market.shelf.firstBase from
      (show market.failures.rows=market.rows by cases a <;> rfl) ▸ source).trans low
  have room : stopRoom C a := by
    refine ⟨Or.inr ?_,?_,?_,?_,?_⟩
    · change max (market.failures.base+market.failures.rows) (market.flags+market.rows)≤ market.flags+market.rows
      exact max_le ((source.trans low).trans (Nat.le_add_right ..)) le_rfl
    · change p.testsStart < p.testsStart+1
      omega
    · change p.testsStart < p.testsStart+1+_+1
      omega
    · change p.testsStart < p.testsStart+1+_+1+_+1
      omega
    · change p.testsStart < p.testsStart+1+(_+1)+(_+1)+(_+1)
      omega
  have stop_eq := prepared_stop_equal C a left right hl hr room w4 (fun b earlier=>same _
    (mode_earlier (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners a b earlier))
  have prior : Below base ((guard C a).apply left) ((guard C a).apply right) := by
    intro x hx
    have sep := (selector_protected (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners a x
      (hx.trans_le (Nat.le_add_right ..))).1.1
    have frame (m : Memory W) : (guard C a).apply m x = m x :=
      ProtocolRAMGeneratedWrite.frame_image ((C).stopAt a) 1 (stop (C).mesh (C).modeAt a) m x (Or.inl sep)
    exact (frame left).trans ((same x hx).trans (frame right).symm)
  have size : rows s≤2^(z+rowFactor s):=row_room s
  have raw : market.rows≤2^W := (Nat.le_add_left ..).trans (Nat.le_of_lt hl.2.1.2.2.2.1)
  have order:=PostLayout.tests_separate (testedBoard p.market.failures p.batch).tests p.testsStart
  apply market.mask_before t _ _ hl.2.1 hr.2.1 prior entered (ballot_owner F c A initial B a)
    (ballot_mask F c A initial B a) stop_eq excess payload rfl failure
    ⟨order.1,order.2.1,order.2.2.1⟩
    (endLow.trans (show market.flags≤(repair C a).tests.excess.out from
      (Nat.le_add_right ..).trans (Nat.le_add_right ..)))
  · cases a <;> exact le_rfl
  · change p.market.rows≤2^p.indexBits
    rw [n,pars.2.2.2.2.2.1]
    exact size
  · change p.market.rows≤2^p.market.failures.rowBits
    rw [n]
    cases a <;> exact size
  · exact raw
  · by_contra! zero
    have h : W=0:=by omega
    simp [h] at w4
  · exact threshold

end Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
end

end OAI
