import OAI.Hierarchy.ProbeFixedFeedWordRoom
import OAI.Hierarchy.ProbeFixedOuterFeedWords
import OAI.Hierarchy.ProbeFixedFeedBill

namespace OAI
/-! # The measured outer injection and cooling boundaries of the billed RAM calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe StockCommit StripChart PurchaseStage
open ThreeFlat.RAM
open scoped Classical BigOperators
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "G" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width

variable (mem : Memory (wordBits z (2^v.W) copies))
  (stock : StockBound.Run (v.nativeChart P z width r banks src tab dst owners) (v.stockBanks P z width)
    mem z (CoreBoard.Stages z (2^v.W)) k (v.keepLimit*width))
  (initialRoom : P.joint.initial + PurchaseInventory.footprint z (CoreBoard.Stages z (2^v.W)) k +
    (sliceROM (P.joint.initial + PurchaseInventory.footprint z (CoreBoard.Stages z (2^v.W)) k)
      v.mesh.reserveSteps (v.keepLimit*width+1)).size ≤ (v.privateArena P z width).first)
  (addressRoom : (v.privateArena P z width).endAddress v.mesh < 2^(wordBits z (2^v.W) copies))
  (headroom : (v.keepLimit+1)*width < 2^(wordBits z (2^v.W) copies))

include stock initialRoom addressRoom headroom in
/-- The native feed charges the exact routed overflow, with each genuine
commodity measured in payload units at its public cap. -/
theorem outer_feed_paid (u : ℕ) (hu : u<v.mesh.inject+v.mesh.cool) :
    let before:=(A).trial C mem u v.mesh.outerFuel
    let finish:=(A).trial C mem (u+1) 0
    let req:=(A).bank.requests width v.mesh.inject u before
    finish.paid=before.paid+pairing (bitStock width (spillBits v.keepLimit width req)) (A).box := by
  let before:=(A).trial C mem u v.mesh.outerFuel
  let finish:=(A).trial C mem (u+1) 0
  let req:=(A).bank.requests width v.mesh.inject u before
  let L:=FeedLayout.atEvent («N»:=N) v.mesh G f P.joint.initial width v.keepLimit (.outer u)
  let next:=phaseState C mem (u+1)
  obtain ⟨_,cut⟩:=outer_feed_slot C mem u hu stock.mounted_all
  have scheduled : Event.feed (.outer u) ∈ events v.mesh := outerFeed_occurs v.mesh hu
  have receipt : finish.paid=before.paid+
      ∑i : FeedLayout.Good z N k,((next (L.overflow+PurchaseInventory.slot i)).val:ℝ)*(A).box i/width := by
    dsimp only [finish,before,AccountColumns.trial,trial_zero,next]
    rw [phase_succ]
    exact v.feed_bill P z width r banks src tab dst owners (.outer u) _ scheduled cut.currentReady
  change finish.paid=before.paid+_
  rw [receipt]
  apply congrArg (before.paid+·)
  change (∑ i : FeedLayout.Good z N k,((next (L.overflow+PurchaseInventory.slot i)).val:ℝ)*(A).box i/width)=
    ∑ i,(bitStock width (spillBits v.keepLimit width req) i)*(A).box i
  apply Finset.sum_congr rfl
  intro i _
  have word : (next (L.overflow+PurchaseInventory.slot i)).val=spillBits v.keepLimit width req i :=
    (v.outer_feed_words P z width r banks src tab dst owners mem stock initialRoom addressRoom headroom u hu i).2
  rw [word]
  unfold bitStock
  ring

include stock initialRoom addressRoom headroom in
/-- The feed field consumed by the outer calendar proof, on the same
physical account as the selected repair, acquisition, and quiet transitions. -/
theorem outer_feed (u : ℕ) (hu : u<v.mesh.inject+v.mesh.cool) :
    (A).bank.BoundaryRead v.mesh.inject (A).payloadWidth v.keepLimit u
      ((A).trial C mem u v.mesh.outerFuel) ((A).trial C mem (u+1) 0) :=
  ⟨fun i=>(v.outer_feed_words P z width r banks src tab dst owners mem stock initialRoom addressRoom headroom u hu i).1,
    (v.outer_feed_paid P z width r banks src tab dst owners mem stock initialRoom addressRoom headroom u hu).le⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
