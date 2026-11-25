import OAI.Hierarchy.ProbeFixedFeedWordRoom
import OAI.Hierarchy.ProbeFixedPaidSlabCell
import OAI.Hierarchy.ProtocolRAMCalendarFeedStock
import OAI.Hierarchy.ProtocolRAMRepairCommodity

namespace OAI
/-! # Native per-commodity overflow at the original checked feed address -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart
open scoped Fin.CommRing Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "lay" => FeedLayout.atEvent («N»:=N) v.mesh G f P.joint.initial width v.keepLimit
local notation "Good" => FeedLayout.Good z N k
local notation "digits" => v.keepLimit*width+1
local notation "tbl" => sliceROM (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps digits

theorem paid_slice_index (mesh : Mesh) (p a j : ℕ) (live : Event.feed (.inner p a j)∈events mesh) :
    j < mesh.reserveSteps := by
  obtain ⟨u,_,hu⟩:=List.mem_flatMap.mp live
  obtain h|h:=List.mem_append.mp hu
  · obtain ⟨t,_,ht⟩:=List.mem_flatMap.mp h
    rcases List.mem_cons.mp ht with ht|ht
    · cases ht
    · obtain ⟨s,hs,inside⟩:=List.mem_flatMap.mp ht
      rcases List.mem_append.mp inside with left|right
      · obtain ⟨i,_,eq⟩:=List.mem_map.mp left
        cases eq
      · have eq:=List.mem_singleton.mp right
        cases eq
        exact List.mem_range.mp hs
  · cases List.mem_singleton.mp h

/-- The feed proof needs the bounded native stock and the loaded public slice
table, including on a tape whose final verdict rejects it. -/
structure PaidFeedStock (mem : Memory W) : Prop where
  nativeStock : StockBound.Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width)
  steps : P.joint.steps=v.mesh.reserveSteps
  digitBudget : P.joint.cap*P.joint.width=v.keepLimit*width
  payload : width≤2^z
  dimension : 2*v.keepLimit+2≤2^z
  endFits : (G).endAddress v.mesh<2^W
  slices : ∃original : Memory W,∀x,(tbl).base≤x→x<(tbl).base+v.mesh.reserveSteps*digits→
    mem x=feedAdvice tbl v.mesh.reserveSteps digits original x

private theorem overflow_le_arrival (old arrival limit : ℕ) (bounded : old ≤ limit) :
    old+arrival-min (old+arrival) limit ≤ arrival := by
  by_cases small : old+arrival ≤ limit
  · rw [Nat.min_eq_left small,Nat.sub_self]
    exact Nat.zero_le _
  · rw [Nat.min_eq_right (by omega)]
    omega

variable (mem : Memory (wordBits z (2^v.W) copies))
  (auth : v.PaidFeedStock P z width r banks src tab dst owners mem)

include auth

/-- Uniformly on a live feed, including a failed purchase's inner feed, only
the fresh ordinary share or the earlier capped reserve can enter overflow. -/
theorem paid_feed_after_of_stock (b : Boundary) (entry : Memory W) (prior tail : List Event)
    (cut : Slot C mem (.feed b) prior tail entry) (i : Good) :
    ((after C (.feed b) entry) ((lay b).overflow+PurchaseInventory.slot i)).val ≤ (v.keepLimit+1)*width := by
  have live : Event.feed b∈events v.mesh := by change _∈events (C).mesh; rw [cut.events]; simp
  have budgets := auth.nativeStock.slot cut
  have initialRoom := v.replay_slice_room P z width auth.steps auth.digitBudget
  obtain ⟨before,stop⟩:=v.stock_feed P z width r banks src tab dst owners b live initialRoom auth.endFits
  have rowRoom : 2^z≤2^W := Nat.pow_le_pow_right (by decide) (by unfold wordBits;omega)
  have room := v.feed_headroom z width auth.payload (by have := auth.dimension;omega)
  have capRoom : v.keepLimit*width<2^W := by
    rw [Nat.add_mul,Nat.one_mul] at room;omega
  have active : PurchaseInventory.stock (lay b).active entry i≤v.keepLimit*width:=budgets.1 i
  cases b with
  | outer u =>
    have one : (if u<v.mesh.inject then slice v.mesh.inject width u*payloadUnit i else 0)≤width := by
      split
      next hu => have h:=FeedLayout.slice_le_total width hu;cases i <;> simp [payloadUnit,h]
      next => omega
    have atRow:=(lay (.outer u)).outer_rows C u entry rfl before stop capRoom rowRoom i
      (FeedLayout.outer_word_room i active room)
    let arrival := if u<v.mesh.inject then slice v.mesh.inject width u*payloadUnit i else 0
    have spill := overflow_le_arrival (PurchaseInventory.stock (lay (.outer u)).active entry i)
      arrival (v.keepLimit*width) active
    rw [atRow.2,Nat.add_mul,Nat.one_mul]
    exact spill.trans (one.trans (Nat.le_add_left ..))
  | inner u a j =>
    have hj := paid_slice_index v.mesh u a j live
    have saved : PurchaseInventory.stock (lay (.inner u a j)).saved entry i≤v.keepLimit*width:=budgets.2 i
    have headroom := v.replay_headroom z width auth.payload (by have := auth.dimension;omega)
    have dataRoom := sliceROM_size (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps digits
    have origin : (tbl).base+v.mesh.reserveSteps*digits≤(G).first := (Nat.add_le_add_left dataRoom _).trans initialRoom
    have count : v.mesh.reserveSteps*digits<2^W := (Nat.le_add_left ..).trans_lt
      (origin.trans_lt ((Nat.le_add_right (G).first _).trans_lt auth.endFits))
    obtain ⟨raw,data⟩:=auth.slices
    have entryData (x : ℕ) (lo : (tbl).base≤x) (hi : x<(tbl).base+v.mesh.reserveSteps*digits) :
        entry x=feedAdvice tbl v.mesh.reserveSteps digits raw x := by
      refine Eq.trans ?_ (data x lo hi)
      rw [←cut.entry]
      apply run_frame C prior mem x cut.prefixReady
      intro ev _
      exact (v.event_prefix P z width r banks src tab dst owners ev x
        ((hi.trans_le origin).trans_le (Nat.le_add_right (G).first _))).1
    have read := (lay (.inner u a j)).inner_rows C u a j entry raw rfl before stop capRoom rowRoom i hj
      (by change _<v.keepLimit*width+1;omega) dataRoom count entryData
      (FeedLayout.reserve_word_room (buy:=entry ((C).modeAt (.outer u a))=3) hj active saved headroom)
    have part := FeedLayout.slice_le_total (PurchaseInventory.stock (lay (.inner u a j)).saved entry i) hj
    let arrival := if entry ((C).modeAt (.outer u a))=3 then
      slice v.mesh.reserveSteps (PurchaseInventory.stock (lay (.inner u a j)).saved entry i) j else 0
    have clipped : arrival ≤ v.keepLimit*width := by
      dsimp only [arrival]
      split
      · exact part.trans saved
      · exact Nat.zero_le _
    have spill := overflow_le_arrival (PurchaseInventory.stock (lay (.inner u a j)).active entry i)
      arrival (v.keepLimit*width) active
    rw [read.2,Nat.add_mul,Nat.one_mul]
    exact spill.trans (clipped.trans (Nat.le_add_right ..))

/-- The column and row on the native boundary traversal are fixed physical
positions in the original feed slab, including columns without a purchase. -/
theorem paid_feed_cell_of_stock (b : Boundary) (live : Event.feed b∈events v.mesh)
    (c : CommodityColumn) (column : c∈(lay b).columns) (i : Fin c.rows) :
    ((checkedOut C ((G).endAddress v.mesh) mem) (c.overflow+i.val)).val≤(v.keepLimit+1)*width := by
  obtain ⟨prior,tail,split⟩:=List.append_of_mem live
  let entry:=Calendar.run C prior mem
  have cut:=slot_of_split C mem (.feed b) prior tail entry split rfl auth.nativeStock.mounted_all
  obtain ⟨l,_,rfl⟩:=List.mem_map.mp column
  let row : Fin (2^z):=⟨i.val,i.isLt⟩
  let n : Fin (PurchaseInventory.footprint z N k):=finProdFinEquiv (l,row)
  let good:Good:=(PurchaseInventory.slotEquiv z N k).symm n
  have loc : PurchaseInventory.slot good=l.val*2^z+i.val := by
    have eq:=congrArg Fin.val ((PurchaseInventory.slotEquiv z N k).apply_symm_apply n)
    change PurchaseInventory.slot good=row.val+2^z*l.val at eq
    simpa [row,Nat.mul_comm,Nat.add_comm] using eq
  have y:=PurchaseInventory.slot_lt good
  have length:=v.feed_room P z width
  have whereAt : ((lay b).column l).overflow+i.val=(lay b).overflow+PurchaseInventory.slot good := by
    rw [loc]
    change (lay b).overflow+l.val*2^z+i.val=_
    omega
  rw [whereAt,v.paid_slab_cell P z width r banks src tab dst owners (.feed b) mem entry prior tail cut _
    (by change (G).base v.mesh (.feed b)+PurchaseInventory.footprint z N k+PurchaseInventory.slot good<_;omega)]
  exact v.paid_feed_after_of_stock P z width r banks src tab dst owners mem auth b entry prior tail cut good

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
