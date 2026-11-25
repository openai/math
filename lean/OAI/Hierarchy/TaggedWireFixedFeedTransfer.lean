import OAI.Hierarchy.TaggedWireFeedMatrix
import OAI.Hierarchy.ProbeFixedWidePaidFeedCell

namespace OAI
/-! # Commodity-width conservation on each original scheduled feed -/

noncomputable section
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

/-- The transfer's active and saved words are read at the given original event.
Kept and spill are the two numerically addressed rows in its actual native output. -/
def dated_feed_transfer (mem : Memory W) (auth : v.PaidFeedStock P z width r banks src tab dst owners mem)
    (b : Boundary) {entry : Memory W} {prior tail : List Event}
    (cut : Slot C mem (.feed b) prior tail entry) : CoreBoard.FeedTransfer.Transfer z (2^v.W) k := by
  have live : Event.feed b∈events v.mesh := by change _∈events (C).mesh; rw [cut.events]; simp
  have budgets:=auth.nativeStock.slot cut
  have initialRoom:=v.replay_slice_room P z width auth.steps auth.digitBudget
  have space:=v.stock_feed P z width r banks src tab dst owners b live initialRoom auth.endFits
  have rowRoom : 2^z≤2^W := Nat.pow_le_pow_right (by decide) (by unfold wordBits; omega)
  have room:=v.feed_headroom z width auth.payload (by have := auth.dimension; omega)
  have capRoom : v.keepLimit*width<2^W := by
    rw [Nat.add_mul,Nat.one_mul] at room
    omega
  cases b with
  | outer u =>
    exact CoreBoard.FeedTransfer.outer (lay (.outer u)) C u entry rfl space.1 space.2 capRoom rowRoom
      (fun i=>FeedLayout.outer_word_room i (budgets.1 i) room)
  | inner u a j =>
    have hj:=paid_slice_index v.mesh u a j live
    have headroom:=v.replay_headroom z width auth.payload (by have :=auth.dimension;omega)
    have dataRoom:=sliceROM_size (P.joint.initial+PurchaseInventory.footprint z stageCount k) v.mesh.reserveSteps digits
    have origin : (tbl).base+v.mesh.reserveSteps*digits≤(G).first := (Nat.add_le_add_left dataRoom _).trans initialRoom
    have lim : v.mesh.reserveSteps*digits<2^W := (Nat.le_add_left ..).trans_lt
      (origin.trans_lt ((Nat.le_add_right (G).first _).trans_lt auth.endFits))
    let fixture:=auth.slices.choose
    have mounted (x : ℕ) (lo : (tbl).base≤x) (hi : x<(tbl).base+v.mesh.reserveSteps*digits) :
        entry x=feedAdvice tbl v.mesh.reserveSteps digits fixture x := by
      rw [←cut.entry]
      apply Eq.trans _ (auth.slices.choose_spec x lo hi)
      apply run_frame C prior mem x cut.prefixReady
      intro ev _
      exact (v.event_prefix P z width r banks src tab dst owners ev x
        ((hi.trans_le origin).trans_le (Nat.le_add_right (G).first _))).1
    exact CoreBoard.FeedTransfer.inner (lay (.inner u a j)) C u a j entry fixture rfl space.1 space.2
      capRoom rowRoom hj (fun i=>Nat.lt_succ_of_le (budgets.2 i)) dataRoom lim mounted
      (fun i=>FeedLayout.reserve_word_room (buy:=entry ((C).modeAt (.outer u a))=3) hj
        (budgets.1 i) (budgets.2 i) headroom)

/-- Original or saved but undelivered bits at the two sides of this boundary. -/
def feed_waiting (b : Boundary) (offset : ℕ) (entry : Memory W) (i : FeedLayout.Good z stageCount k) :=
  match b with
  | .outer u => held v.mesh.inject width (u+offset)*payloadUnit i
  | .inner u a j => if entry ((C).modeAt (.outer u a))=3
      then held v.mesh.reserveSteps (PurchaseInventory.stock (lay (.inner u a j)).saved entry i) (j+offset)
      else 0

theorem dated_feed_reads (mem : Memory W) (auth : v.PaidFeedStock P z width r banks src tab dst owners mem)
    (b : Boundary) {entry : Memory W} {prior tail : List Event} (cut : Slot C mem (.feed b) prior tail entry)
    (i : FeedLayout.Good z stageCount k) :
    let T:=v.dated_feed_transfer P z width r banks src tab dst owners mem auth b cut
    let wait:=v.feed_waiting P z width r banks src tab dst owners b
    T.old i=wait 0 entry i ∧ T.held i=wait 1 entry i ∧
    T.active i=PurchaseInventory.stock (lay b).active entry i ∧
    T.kept i=(after C (.feed b) entry ((lay b).kept+PurchaseInventory.slot i)).val ∧
    T.spill i=(after C (.feed b) entry ((lay b).overflow+PurchaseInventory.slot i)).val := by
  cases b <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem dated_feed_saved_spill (mem : Memory W) (auth : v.PaidFeedStock P z width r banks src tab dst owners mem)
    (b : Boundary) {entry : Memory W} {prior tail : List Event} (cut : Slot C mem (.feed b) prior tail entry)
    (i : FeedLayout.Good z stageCount k) :
    (v.dated_feed_transfer P z width r banks src tab dst owners mem auth b cut).spill i=
      (checkedOut C ((G).endAddress v.mesh) mem ((lay b).overflow+PurchaseInventory.slot i)).val := by
  have afterWord:=(v.dated_feed_reads P z width r banks src tab dst owners mem auth b cut i).2.2.2.2
  rw [afterWord]
  apply congrArg Fin.val
  apply Eq.symm
  apply v.paid_slab_cell P z width r banks src tab dst owners (.feed b) mem entry prior tail cut
  have slot:=PurchaseInventory.slot_lt i
  have total:=v.feed_room P z width
  change (G).base v.mesh (.feed b)+PurchaseInventory.footprint z stageCount k+PurchaseInventory.slot i<
    (G).base v.mesh (.feed b)+(G).stride
  omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
