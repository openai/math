import OAI.Hierarchy.ProbeFixedPaidDirectoryShapes
import OAI.Hierarchy.ProbeFixedPaidAmountFields
import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProtocolRAMPaidSliceFits

namespace OAI
/-! # Mount every original width transaction in the native calendar's returned memory -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockBound StockCommit
open CoreRoute CatalystArchive
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
set_option quotPrecheck false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ)
local notation "D" => 2^v.W
local notation "N" => Stages z D
local notation "W" => wordBits z D copies
local notation "G" => v.privateArena P z width
local notation "r" => Fintype.card (Slots z D k)
local notation "fmt" => v.nativeFormats P z width
local notation "H" => v.publicHeader P z width
local notation "tre" => v.nativeTrees P z width
local notation "bs" => v.nativeBoards P z width
local notation "role" => fun a=> (StripChart.header F bs a).fieldTerm
local notation "ids" => StripChart.id F bs P.catalogue
local notation "layout" => FeedLayout.atEvent («N»:=N) v.mesh G fmt P.joint.initial width v.keepLimit
local notation "feeds" => feedColumns («N»:=N) v.mesh G fmt P.joint.initial width v.keepLimit
local notation "O" => v.catalystPairOwners P z width
local notation "T" => v.catalystPairParity P z width
local notation "attempts" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel

theorem paid_feed_archive (b : Boundary) (live : Event.feed b∈events v.mesh) (c : CommodityColumn) (hc : c∈feeds b) :
    c.overflow+c.rows≤(G).endAddress v.mesh ∧ c.rows≤PurchaseInventory.footprint z N k := by
  change c∈(List.finRange (FeedLayout.lanes N k)).map ((layout b).column) at hc
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp hc
  have span:=Nat.mul_le_mul_right (2^z) (show i.val+1≤FeedLayout.lanes N k from i.isLt)
  have row:=Nat.mul_le_mul_right (2^z) (show 1≤FeedLayout.lanes N k by simp [FeedLayout.lanes])
  rw [Nat.add_mul,one_mul] at span
  rw [one_mul] at row
  have stock : FeedLayout.lanes N k*2^z=PurchaseInventory.footprint z N k:=rfl
  rw [stock] at span row
  have packed:=v.feed_room P z width
  have endAt:=(G).within v.mesh (.feed b) live
  change (G).base v.mesh (.feed b)+PurchaseInventory.footprint z N k+i.val*2^z+2^z≤_ ∧ _
  exact ⟨by omega,row⟩


private theorem fit_before (bank : Bank) {w bound : ℕ} (endAt : bank.base+bank.size≤bound) (room : bound<2^w) :
    bank.Fits w bound :=
  ⟨Nat.two_pow_pos _,((Nat.le_add_left ..).trans endAt).trans_lt room,endAt⟩

/-- The only source-side premises concern individual native controller expressions.
The remaining banks, archive fields, scratch space, and readbacks are proved here
from this same original fixed layout and its physical memory. -/
theorem paid_mounted_at (stock : Bank) (stride count n bits : ℕ) (x : Source) (recipe : Recipes)
    (order : Orders z D k) (owners : Bank) (m : Memory W) :
    let page:=TerminalLayout.pageBits v.mesh G stock stride P.catalogue.rows r count n
    let banks:=TerminalLayout.settlement page stock
    let src:=TerminalLayout.source page
    let tab:=TerminalLayout.table page
    let dst:=TerminalLayout.destination page
    let sink:=P.catalogue.sink r banks src tab dst owners
    let C:=v.nativeChart P z width r banks src tab dst owners
    let chk:=checkedOut C ((G).endAddress v.mesh) m
    let B:=banks.width.base
    let core:=v.paidSpillPath P z width recipe x order
    let boundary:=v.paidFeedPath P z width x layout
    (H).Resident m → Calendar.mounted C (events v.mesh) m →
    PaidPairDirectory.Reads O T r chk → 28*2^page<2^W →
    v.catalystStaticStart P z width≤(G).first →
    Safe x v.sampler z v.W k attempts W B →
    recipe.kind.Fits W B ∧ recipe.mode.Fits W B ∧ recipe.operand.Fits W B →
    (∀a,Event.attempt a∈events v.mesh→
      ((fmt a).labelSource sink P.catalogue.idBase (role a) (ids a)).edge.Fits W B ∧
      (tre a).edge.Fits W B ∧ (tre a).sourceRow.Fits W B ∧
      ∀ t∈(tre a).catalystMate,t.1.Fits W B ∧ t.2.Fits W B) →
    PaidWidths.Mounted banks.width P.catalogue.rows src
      (paidSlices v.mesh fmt feeds sink P.catalogue.idBase role ids tre core boundary bits) chk := by
  intro h banks src tab dst sink C chk B core boundary pub run stored room staticAt safe recipeFit old
  have num : B=2^h:=by change 1*_= _; exact Nat.one_mul _
  have cap : TerminalLayout.footprint v.mesh G stock stride P.catalogue.rows r count n<2^h:=Nat.lt_log2_self
  unfold TerminalLayout.footprint at cap
  have endAt : (G).endAddress v.mesh≤B := by omega
  have initial : (G).first≤(G).endAddress v.mesh := Nat.le_add_right ..
  have routes : r≤B := by omega
  have limits : B<2^W := by change 28*2^h<2^W at room;omega
  have wide : 0<W := by
    by_contra! eq
    have one : 0<2^h := Nat.two_pow_pos _
    rw [show W=0 by omega] at limits
    omega
  have pairs:=v.paid_pair_rows P z width sink P.catalogue.idBase role ids feeds recipe x order layout bits banks src tab dst owners
    ((G).endAddress v.mesh) m pub run initial (by change 28*2^h<2^W at room;omega) wide stored
  have shape:=v.paid_pair_geometry P z width sink P.catalogue.idBase role ids feeds recipe x order layout bits B
    (initial.trans endAt) (staticAt.trans (initial.trans endAt)) routes
  have prior := earlyFits recipe x order O T safe recipeFit
  have feed (b : Boundary) (c : CommodityColumn) := lane_fits x (decodeLane (feedLane (layout b) c)) O T safe
  have cash := v.paid_amount_fields P z width stock stride count n fmt (fun _=>rfl) feeds sink P.catalogue.idBase
    role ids tre core boundary bits limits
    (fun a live=>⟨(old a live).2.2.1,prior.2,fun t ht=>((old a live).2.2.2 t ht).1⟩)
    (fun b live c hc=>⟨(v.paid_feed_archive P z width b live c hc).1,
      (v.paid_feed_archive P z width b live c hc).2,(feed b c).2⟩)
  refine PaidEventDirectory.mounted ?_ pairs
  intro s hs
  obtain ⟨owner,tag,quantity⟩:=shape s hs
  refine s.fits_of_fields banks.width ?_ (cash s hs) (fit_before _ owner limits) (fit_before _ tag limits) ?_ ?_
  · obtain ⟨event,live,entry⟩:=List.mem_flatMap.mp hs
    cases event with
    | feed b =>
      obtain ⟨c,_,rfl⟩:=List.mem_map.mp entry
      exact (feed b c).1
    | attempt a =>
      have data:=old a live
      cases hm : (tre a).catalystMate with
      | none =>
        simp [eventSlices,Format.paidSlices,Format.mateSlices,hm] at entry
        rcases entry with rfl|rfl|rfl
        · exact data.1
        · exact data.2.1
        · exact prior.1
      | some t =>
        simp [eventSlices,Format.paidSlices,Format.mateSlices,hm] at entry
        rcases entry with rfl|rfl|rfl|rfl
        · exact data.1
        · exact (data.2.2.2 t (by simp [hm])).2
        · exact data.2.1
        · exact prior.1
  · change B+P.catalogue.rows<9*2^h
    omega
  · change 9*2^h+2*s.count<2^W
    change 28*2^h<2^W at room
    omega


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
