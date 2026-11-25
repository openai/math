import OAI.Hierarchy.ProbeFixedPostings

namespace OAI
/-! # Billing the physical commodity overflow at each scheduled feed -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart
open scoped BigOperators Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners

/-- The change in paid stock is exactly the spill emitted by this feed, valued
at the physical commodity's route price and normalized by the payload width. -/
theorem feed_bill (boundary : Boundary) (entry : Memory W)
    (scheduled : Event.feed boundary∈events v.mesh) (run : ready C (.feed boundary) entry) :
    let e:=Event.feed boundary
    let states:=Succession v.mesh e
    let L:=FeedLayout.atEvent («N»:=N) v.mesh (v.privateArena P z width) (v.nativeFormats P z width)
      P.joint.initial width v.keepLimit boundary
    let out:=after C e entry
    ((A).read states.2 out).paid=((A).read states.1 entry).paid+
      ∑i : FeedLayout.Good z N k,((out (L.overflow+PurchaseInventory.slot i)).val:ℝ)*(A).box i/width := by
  intro e states L out
  have sale:=v.append_paid P z width r banks src tab dst owners e entry scheduled run
  let key : FeedLayout.Good z N k→ℕ:=fun _=>0
  let price : FeedLayout.Good z N k→ℕ→ℝ:=fun i _=>(A).box i
  have read:=spillRows_bill L key price out width 0
  change ((A).read states.2 out).paid=((A).read states.1 entry).paid+(spillRows L key price).bill width out at sale
  rw [sale,read]
  simp only [price,Charges.net,Nat.cast_zero,mul_zero,zero_div,sub_zero,add_zero]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
