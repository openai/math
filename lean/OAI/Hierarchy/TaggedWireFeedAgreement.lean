import OAI.Hierarchy.TaggedWireFixedFeedTransfer
import OAI.Hierarchy.TaggedWirePublicShelf
import OAI.Hierarchy.ProbeFixedWideMountAgreement

namespace OAI
/-! # A feed reads identical physical operands on every continuation of one cursor -/
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart
open scoped Fin.CommRing Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "stageCount" => CoreBoard.Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "lay" => FeedLayout.atEvent (N := stageCount) v.mesh G f P.joint.initial width v.keepLimit
local notation "digits" => v.keepLimit*width+1
local notation "tbl" => sliceROM (P.joint.initial+PurchaseInventory.footprint z stageCount k) v.mesh.reserveSteps digits

theorem dated_transfer_agrees (b : Boundary) {m m' entry entry' : Memory W} {prior tail prior' tail'}
    (checked : v.PaidFeedStock P z width r banks src tab dst owners m)
    (checked' : v.PaidFeedStock P z width r banks src tab dst owners m')
    (a : Slot C m (.feed b) prior tail entry) (a' : Slot C m' (.feed b) prior' tail' entry')
    (pre : PrefixAgreement.Low ((G).base v.mesh (.feed b)) entry entry')
    (post : PrefixAgreement.Low ((G).base v.mesh (.feed b)+(G).stride)
      (after C (.feed b) entry) (after C (.feed b) entry')) :
    v.dated_feed_transfer P z width r banks src tab dst owners m checked b a=
      v.dated_feed_transfer P z width r banks src tab dst owners m' checked' b a' := by
  let L:=lay b
  have seen : Event.feed b∈events v.mesh:=by change _∈events (C).mesh;rw [a.events];simp
  have room:=(v.stock_feed P z width r banks src tab dst owners b seen
    (v.replay_slice_room P z width checked.steps checked.digitBudget) checked.endFits).1
  have work:=v.feed_room P z width
  have baseEq : L.kept=(G).base v.mesh (.feed b):=rfl
  have scalar (base : Nat) (fits : base+PurchaseInventory.footprint z stageCount k≤L.kept) (i : FeedLayout.Good z stageCount k) :
      PurchaseInventory.stock base entry i=PurchaseInventory.stock base entry' i:=by
    unfold PurchaseInventory.stock
    have inSlot:=PurchaseInventory.slot_lt i
    exact congrArg Fin.val (pre _ (by omega))
  have wait (offset : Nat) (i : FeedLayout.Good z stageCount k) :
      v.feed_waiting P z width r banks src tab dst owners b offset entry i=
        v.feed_waiting P z width r banks src tab dst owners b offset entry' i:=by
    cases b with
    | outer u=>rfl
    | inner u p j=>
      have mode:=room.mode u p j rfl
      have old:=scalar _ room.saved i
      simp only [feed_waiting]
      have modeEarlier : (C).modeAt (.outer u p)<(G).base v.mesh (.feed (.inner u p j)) := mode
      rw [pre _ modeEarlier,old]
  let first:=v.dated_feed_reads P z width r banks src tab dst owners m checked b a
  let second:=v.dated_feed_reads P z width r banks src tab dst owners m' checked' b a'
  have fit (i : FeedLayout.Good z stageCount k) :
      L.kept+PurchaseInventory.slot i<(G).base v.mesh (.feed b)+(G).stride ∧
      L.overflow+PurchaseInventory.slot i<(G).base v.mesh (.feed b)+(G).stride :=by
    have unit:=PurchaseInventory.slot_lt i
    change L.kept+_<_ ∧ L.kept+PurchaseInventory.footprint z stageCount k+_ < _
    omega
  have same (i : FeedLayout.Good z stageCount k) :=
    And.intro (post _ (fit i).1) (post _ (fit i).2)
  have ext {t t' : CoreBoard.FeedTransfer.Transfer z (2^v.W) k}
      (a : t.old=t'.old) (b : t.active=t'.active) (c : t.held=t'.held)
      (d : t.kept=t'.kept) (e : t.spill=t'.spill) : t=t' := by
    cases t;cases t';simp_all
  apply ext <;> funext i
  · exact (first i).1.trans ((wait 0 i).trans (second i).1.symm)
  · exact (first i).2.2.1.trans ((scalar _ room.active i).trans (second i).2.2.1.symm)
  · exact (first i).2.1.trans ((wait 1 i).trans (second i).2.1.symm)
  · exact (first i).2.2.2.1.trans ((congrArg Fin.val (same i).1).trans (second i).2.2.2.1.symm)
  · exact (first i).2.2.2.2.trans ((congrArg Fin.val (same i).2).trans (second i).2.2.2.2.symm)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
