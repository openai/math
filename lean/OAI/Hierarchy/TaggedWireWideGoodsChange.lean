import OAI.Hierarchy.TaggedWireFixedGoodsChange
import OAI.Hierarchy.TaggedWireDatedLedger

namespace OAI
/-! # Chronological input and output widths at the actual signed checkout -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl

local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tbl" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "C" => v.wideSignedChart h width stock
local notation "bs" => v.stockBanks P h width
local notation "es" => events v.mesh
local notation "order" => wideRouteOrder h D k
local notation "good" => Commodity (Fin (2^h)) N k

theorem wire_quantity_at (j : ℕ) (m : Memory w) (i : good) :
    v.wireGoodsAt h width j m i=v.datedQuantity P h width r old src tbl dst owners j m i := Nat.add_assoc _ _ _

theorem wire_feed_quantities (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (late : v.wideStockHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (dimension : 2*v.keepLimit+2≤2^h)
    (u : ℕ) (on : u<(es).length) (b : Boundary) (atFeed : (es)[u]=.feed b)
    {entry : Memory w} {prior tail : List Event}
    (cut : Slot C (v.wideSignedMidAt h width size stock M π order raw) (.feed b) prior tail entry) (i : good) :
    let mem:=v.wideSignedMidAt h width size stock M π order raw
    let auth:=v.wide_paid_feed_stock h width size extent M π raw late budget small dimension
    let T:=v.dated_feed_transfer P h width r old src tbl dst owners mem auth b cut
    let passive:=v.feedPassive (z:=h) width b i
    v.wireGoodsAt h width u entry i=passive+T.old i+T.active i ∧
    v.wireGoodsAt h width (u+1) (after C (.feed b) entry) i=passive+T.held i+T.kept i ∧
    T.spill i=(v.wideSignedCheckoutAt h width size stock M π order raw
      ((FeedLayout.atEvent («N» := N) v.mesh A (v.nativeFormats P h width) (P).joint.initial width v.keepLimit b).overflow+
        PurchaseInventory.slot i)).val := by
  dsimp only
  let auth:=v.wide_paid_feed_stock h width size extent M π raw late budget small dimension
  have eqn:=v.dated_feed_quantities P h width r old src tbl dst owners _ auth u on b atFeed cut i
  rw [v.wire_quantity_at,v.wire_quantity_at]
  exact ⟨eqn.1,eqn.2,v.dated_feed_saved_spill P h width r old src tbl dst owners _ auth b cut i⟩

theorem wire_attempt_quantities (u : ℕ) (on : u<(es).length) (a : Attempt) (atTrial : (es)[u]=.attempt a)
    {mem entry : Memory w} {prior tail : List Event}
    (cut : Slot C mem (.attempt a) prior tail entry) (i : good) :
    let pass:=v.attemptPassive P h width r old src tbl dst owners a entry i
    let out:=after C (.attempt a) entry
    v.wireGoodsAt h width u entry i=pass+PurchaseInventory.stock ((bs).previous v.mesh (.attempt a)) entry i ∧
    v.wireGoodsAt h width (u+1) out i=pass+
      v.newlyHeld P h width r old src tbl dst owners a out i+PurchaseInventory.stock ((bs).active (.attempt a)) out i := by
  dsimp only
  rw [v.wire_quantity_at,v.wire_quantity_at]
  exact v.dated_attempt_quantities P h width r old src tbl dst owners u on a atTrial cut i

theorem wire_attempt_stock_le (u : ℕ) (on : u<(es).length) (a : Attempt) (atTrial : (es)[u]=.attempt a)
    {mem entry : Memory w} {prior tail : List Event}
    (cut : Slot C mem (.attempt a) prior tail entry) (i : good) :
    PurchaseInventory.stock ((bs).previous v.mesh (.attempt a)) entry i≤v.wireGoodsAt h width u entry i := by
  rw [(v.wire_attempt_quantities h width u on a atTrial cut i).1]
  exact Nat.le_add_left ..

/-- The virtual last checkout reads the last published active bank. Both
the original injection and the entire earlier reserve have finished. -/
theorem wire_terminal_source (m : Memory w) (i : good) :
    v.wireGoodsAt h width (es).length m i=PurchaseInventory.stock (stock).base m i := by
  let phaseEnd:=v.mesh.inject+v.mesh.cool
  have location : position v.mesh (.attempt (.outer phaseEnd 0))=(es).length := by
    simp [position,trialBase,phaseSize,trialSize,sliceSize,event_count,phaseEnd]
  have reg : DatedGoods.previous v.mesh bs (es).length=(stock).base := by
    change DatedGoods.previous v.mesh bs (es).length=
      previousStock v.mesh (P).joint.initial (publishedStock v.mesh A (v.nativeFormats P h width))
        (.attempt (.outer phaseEnd 0))
    exact (congrArg (DatedGoods.previous v.mesh bs) location).symm
  have stop : held v.mesh.inject width phaseEnd=0 := by
    calc
      held v.mesh.inject width phaseEnd=held v.mesh.inject width v.mesh.inject := by
        simp [held,phaseEnd]
      _=0:=held_finish _ _ v.clock.inject_pos
  unfold wireGoodsAt
  rw [List.getElem?_eq_none (Nat.le_refl _),reg]
  change PurchaseInventory.stock (stock).base m i+held v.mesh.inject width phaseEnd*payloadUnit i+0=_
  simp [stop]

theorem wire_terminal_goods (mem : Memory w) (i : good) :
    v.wireGoodsAt h width (es).length (run C es mem) i=
      (checkedOut C ((A).endAddress v.mesh) mem ((stock).base+PurchaseInventory.slot i)).val := by
  rw [v.wire_terminal_source]
  have idx:=PurchaseInventory.slot_lt i
  have bits:=ProtocolRAMPurchaseSampler.lt_span (PurchaseInventory.footprint h N k)
  have cap : (stock).base+(stock).size≤(A).endAddress v.mesh:=v.fixedTerminalStock_end P h width
  have room : (stock).base+PurchaseInventory.slot i<(A).endAddress v.mesh := by
    change (stock).base+ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint h N k)≤_ at cap
    omega
  have frame : checkedOut C ((A).endAddress v.mesh) mem ((stock).base+PurchaseInventory.slot i)=
      run C es mem ((stock).base+PurchaseInventory.slot i) :=
    ProtocolRAMGeneratedWrite.frame_image _ 1 _ _ _ (.inl room)
  exact congrArg Fin.val frame.symm

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
