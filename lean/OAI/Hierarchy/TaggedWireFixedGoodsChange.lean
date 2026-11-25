import OAI.Hierarchy.TaggedWireGoodsContour
import OAI.Hierarchy.TaggedWireFixedFeedTransfer

namespace OAI
/-! # The actual active, uninjected and purchased goods on both sides of every instruction block -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart
open scoped Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "bs" => v.stockBanks P z width
local notation "es" => events v.mesh
local notation "Good" => FeedLayout.Good z N k

def datedQuantity (u : ℕ) (m : Memory W) (i : Good) : ℕ :=
  PurchaseInventory.stock (DatedGoods.previous v.mesh bs u) m i+
    DatedGoods.pending v.mesh bs (C).modeAt width ((es)[u]?) m i

/-- Every mutable inner date can read the born saved word and the exact
mode that enabled it before and after its own actual edit. -/
theorem dated_parent_held (e : Event) {mem entry : Memory W} {prior tail : List Event}
    (cut : Slot C mem e prior tail entry) (p a : ℕ) (matched : StockBound.parent e=some (.outer p a))
    (j : ℕ) (i : Good) :
    DatedGoods.purchased v.mesh bs (C).modeAt p a j (after C e entry) i=
      DatedGoods.purchased v.mesh bs (C).modeAt p a j entry i := by
  have live : e∈es := by change e∈events (C).mesh; rw [cut.events]; simp
  have earlier := (StockBound.parent_before v.mesh e (.outer p a) live matched).2
  have apart := (A).apart v.mesh earlier
  have frame (x : ℕ) (inside : x<(A).base v.mesh (.attempt (.outer p a))+(A).stride) :
      after C e entry x=entry x := after_frame C e entry x cut.currentReady
        (v.event_prefix P z width r banks src tab dst owners e x (inside.trans_le apart)).1
  have tag : (C).modeAt (.outer p a)<(A).base v.mesh (.attempt (.outer p a))+(A).stride :=
    v.stock_mode_room P z width (.outer p a)
  have idx:=PurchaseInventory.slot_lt i
  have cap:=v.stock_post_span P z width (.outer p a)
  have inside : (bs).saved (.outer p a)+PurchaseInventory.slot i<
      (A).base v.mesh (.attempt (.outer p a))+(A).stride := by
    change (f (.outer p a)).pricedArea.output+(f (.outer p a)).pricedArea.goods+PurchaseInventory.slot i<_
    omega
  simp only [DatedGoods.purchased,PurchaseInventory.stock,frame _ tag,frame _ inside]

def feedPassive (b : Boundary) (i : Good) : ℕ :=
  match b with
  | .outer _ => 0
  | .inner p _ _ => DatedGoods.original v.mesh width p i

/-- The unchanged inventory is the still-uninjected original payload during
an inner feed. The transfer gives all four remaining chronological stock words. -/
theorem dated_feed_quantities (mem : Memory W) (auth : v.PaidFeedStock P z width r banks src tab dst owners mem)
    (u : ℕ) (on : u<(es).length) (b : Boundary) (atFeed : (es)[u]=.feed b)
    {entry : Memory W} {prior tail : List Event} (cut : Slot C mem (.feed b) prior tail entry) (i : Good) :
    let T:=v.dated_feed_transfer P z width r banks src tab dst owners mem auth b cut
    let passive:=v.feedPassive (z:=z) width b i
    v.datedQuantity P z width r banks src tab dst owners u entry i=passive+T.old i+T.active i ∧
    v.datedQuantity P z width r banks src tab dst owners (u+1) (after C (.feed b) entry) i=
      passive+T.held i+T.kept i := by
  have prev:=DatedGoods.at_date v.mesh bs (C).modeAt width u on entry i
  have next:=DatedGoods.after_date v.mesh bs (C).modeAt width u on (after C (.feed b) entry) i
  dsimp only at prev next
  rw [atFeed] at prev next
  obtain ⟨old,remain,active,kept,_⟩:=v.dated_feed_reads P z width r banks src tab dst owners mem auth b cut i
  dsimp only
  unfold datedQuantity
  rw [prev,next,old,remain,active,kept]
  cases b with
  | outer p =>
    have outerSum (balance waiting : ℕ) : balance+waiting=0+waiting+balance := by
      rw [Nat.zero_add, Nat.add_comm balance waiting]
    exact ⟨outerSum _ _, outerSum _ _⟩
  | inner p a j =>
    have same:=v.dated_parent_held P z width r banks src tab dst owners (.feed (.inner p a j)) cut p a rfl (j+1) i
    simp only [feedPassive,DatedGoods.entering,DatedGoods.leaving,same]
    exact ⟨Nat.add_comm _ _, Nat.add_comm _ _⟩

/-- The old, externally entering injection stays frozen during every attempt.
Only a real outer purchase can introduce its just-published saved register. -/
def attemptPassive (a : Attempt) (m : Memory W) (i : Good) : ℕ :=
  DatedGoods.entering v.mesh bs (C).modeAt width (.attempt a) m i

def newlyHeld : Attempt→Memory W→Good→ℕ
  | .outer p a,m,i => if 0<v.mesh.reserveSteps then
      DatedGoods.purchased v.mesh bs (C).modeAt p a 0 m i else 0
  | .inner _ _ _ _,_,_ => 0

theorem newlyHeld_outer (p a : ℕ) (m : Memory W) (i : Good) :
    v.newlyHeld P z width r banks src tab dst owners (.outer p a) m i=
      if m ((C).modeAt (.outer p a))=3 then PurchaseInventory.stock ((bs).saved (.outer p a)) m i else 0 := by
  simp [newlyHeld,DatedGoods.purchased,v.clock.reserve_pos,held_start]

theorem dated_attempt_quantities (u : ℕ) (on : u<(es).length) (a : Attempt) (atTrial : (es)[u]=.attempt a)
    {mem entry : Memory W} {prior tail : List Event} (cut : Slot C mem (.attempt a) prior tail entry) (i : Good) :
    let pass:=v.attemptPassive P z width r banks src tab dst owners a entry i
    let out:=after C (.attempt a) entry
    v.datedQuantity P z width r banks src tab dst owners u entry i=
      pass+PurchaseInventory.stock ((bs).previous v.mesh (.attempt a)) entry i ∧
    v.datedQuantity P z width r banks src tab dst owners (u+1) out i=
      pass+v.newlyHeld P z width r banks src tab dst owners a out i+PurchaseInventory.stock ((bs).active (.attempt a)) out i := by
  have prev:=DatedGoods.at_date v.mesh bs (C).modeAt width u on entry i
  have next:=DatedGoods.after_date v.mesh bs (C).modeAt width u on (after C (.attempt a) entry) i
  dsimp only at prev next
  rw [atTrial] at prev next
  unfold datedQuantity
  dsimp only
  rw [prev,next]
  constructor
  · exact Nat.add_comm _ _
  · cases a with
    | outer p t => simp only [attemptPassive,DatedGoods.entering,DatedGoods.leaving,newlyHeld];ac_rfl
    | inner p t j b =>
      have eqn:=v.dated_parent_held P z width r banks src tab dst owners (.attempt (.inner p t j b))
        cut p t rfl j i
      simp only [attemptPassive,DatedGoods.entering,DatedGoods.leaving,newlyHeld,Nat.add_zero,eqn]
      exact Nat.add_comm _ _

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
