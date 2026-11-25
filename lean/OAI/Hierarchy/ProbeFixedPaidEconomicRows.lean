import OAI.Hierarchy.ProbeFixedStockWindow
import OAI.Hierarchy.ProbeFixedCatalystHeaders
import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProtocolRAMCalendarStripBuyIdle
import OAI.Hierarchy.ProtocolRAMCalendarStripTreeBudget
import OAI.Hierarchy.ProtocolRAMPaidEventDirectory

namespace OAI
/-! # Ordinal and parity rows of the installed ordinary and broadcast events -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockBound StockCommit StripDirectory CatalogueRows
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
set_option quotPrecheck false
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ)
local notation "W" => wordBits z (2^v.W) copies
local notation "G" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "fmt" => v.nativeFormats P z width
local notation "H" => v.publicHeader P z width
local notation "tre" => v.nativeTrees P z width
local notation "origin" => v.seed P z width
local notation "old" => v.sized origin width
local notation "site" => v.located origin P width
local notation "rows" => treeRows site v.mesh P.catalogue P.routes F
local notation "payload" => PayloadStrip.edgeCount (CoreBoard.Stages z (2^v.W))

theorem paidTreePage_eq (base n : ℕ) :
    treePage site v.mesh P.catalogue P.routes F base n=treePage old v.mesh P.catalogue P.routes F base n := by
  have changeRows : rows=treeRows old v.mesh P.catalogue P.routes F := by
    funext a
    simp only [treeRows_eq]; rfl
  let pack (jobRows : Attempt→ℕ) : PortROM.Table (events v.mesh).length :=
    let sizes:=fun i : Fin (events v.mesh).length=>match (events v.mesh)[i] with
      | .attempt a=>jobRows a | .feed _=>0
    ⟨base,sizes,Fintype.card (Strip.TreeLink n k),Finset.univ.sup sizes,fun i=>Finset.le_sup (Finset.mem_univ i)⟩
  exact congrArg pack changeRows

private theorem fetched (base n : ℕ) (a : Attempt) (occurs : Event.attempt a∈events v.mesh) :
    let table:=treePage site v.mesh P.catalogue P.routes F base n
    let i : Fin (events v.mesh).length:=⟨(events v.mesh).idxOf (.attempt a),List.idxOf_lt_length_of_mem occurs⟩
    table.header i=treeHeader (pageStart table v.mesh a) (rows a) n k := by
  intro table i
  have date : (events v.mesh)[i]=Event.attempt a:=List.getElem_idxOf i.isLt
  have atRow : table.rows i=rows a := by
    change (match (events v.mesh)[i] with | .attempt t=>rows t | .feed _=>0)=_
    rw [date]
  change PortHeader.mk _ (table.rows i) _=_
  rw [atRow]; rfl

def paidTreeHeader (a : Attempt) (occurs : Event.attempt a∈events v.mesh) : PortHeader :=
  let i : Fin (events v.mesh).length:=⟨(events v.mesh).idxOf (.attempt a),List.idxOf_lt_length_of_mem occurs⟩
  match a with
  | .outer _ _=>(H).payloadTree.header i
  | .inner _ _ _ _=>(H).boughtTree.header i

set_option maxHeartbeats 800000 in
theorem paid_economic_headers (a : Attempt) (occurs : Event.attempt a∈events v.mesh) :
    let o:=(H).ports.header 0
    let h:=paidTreeHeader v P z width a occurs
    ((fmt a).stockSource.owner=o.owner ∧ (fmt a).stockSource.parity=o.parity ∧
      (fmt a).pricedArea.occurrences=o.count ∧ o.stop≤(G).first) ∧
    ((tre a).owner=h.owner ∧ (tre a).parity=h.parity ∧ (tre a).positions=h.count ∧ h.stop≤(G).first) := by
  intro o h
  have chart:=(shape_header F B v.mesh G P.joint.initial a).1
  have actual : StripChart.header F B a=o :=
    (congrArg (fun s=>StripChart.header F s a) (v.catalyst_boards P z width)).symm.trans
      (v.catalyst_header P z width a).symm
  have same := chart.trans actual
  have sealed:=occurrence_sealed F B v.mesh G P.joint.initial a
  have owner:=congrArg (fun f=>f.stockSource.owner) sealed
  have parity:=congrArg (fun f=>f.stockSource.parity) sealed
  have n := (v.occurrence_count P z width a).trans (congrArg PortHeader.count actual)
  refine ⟨⟨owner.symm.trans (congrArg PortHeader.owner same),parity.symm.trans (congrArg PortHeader.parity same),n,
    ((H).ports.end_le 0).trans (v.stock_port_room P z width)⟩,?_⟩
  let i : Fin (events v.mesh).length:=⟨(events v.mesh).idxOf (.attempt a),List.idxOf_lt_length_of_mem occurs⟩
  let page:=payloadPage site v.mesh P.catalogue P.routes F (H).payloadTree.base
  have pageEq : page=(H).payloadTree := paidTreePage_eq v P z width (H).payloadTree.base payload
  have secondEq : boughtPage site v.mesh P.catalogue P.routes F (H).payloadTree.base=(H).boughtTree := by
    change treePage site v.mesh P.catalogue P.routes F page.stop _=_
    rw [pageEq]
    exact paidTreePage_eq v P z width (H).payloadTree.stop (ChainStrip.edgeCount v.depth)
  have atP:=fetched v P z width (H).payloadTree.base payload a occurs
  have atB:=fetched v P z width page.stop (ChainStrip.edgeCount v.depth) a occurs
  change page.header i=treeHeader (pageStart page v.mesh a) (rows a) payload k at atP
  change (boughtPage site v.mesh P.catalogue P.routes F (H).payloadTree.base).header i=
    treeHeader (pageStart (boughtPage site v.mesh P.catalogue P.routes F (H).payloadTree.base) v.mesh a)
      (rows a) (ChainStrip.edgeCount v.depth) k at atB
  have firstHeader := (congrArg (fun t : PortROM.Table (events v.mesh).length=>t.header i) pageEq).symm.trans atP
  have lastHeader := (congrArg (fun t : PortROM.Table (events v.mesh).length=>t.header i) secondEq).symm.trans atB
  have economic : (H).stop≤(G).first := (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P z width)
  have pEnd : (H).payloadTree.stop≤(H).stop := Nat.le_add_right (H).payloadTree.stop _
  cases a with
  | outer p a =>
    have endAt := ((H).payloadTree.end_le i).trans (pEnd.trans economic)
    change _= ((H).payloadTree.header i).owner ∧ _=((H).payloadTree.header i).parity ∧
      _=((H).payloadTree.header i).count ∧ ((H).payloadTree.header i).stop≤_
    exact ⟨congrArg PortHeader.owner firstHeader.symm,congrArg PortHeader.parity firstHeader.symm,
      congrArg PortHeader.count firstHeader.symm,endAt⟩
  | inner p a j u =>
    have endAt := ((H).boughtTree.end_le i).trans economic
    change _= ((H).boughtTree.header i).owner ∧ _=((H).boughtTree.header i).parity ∧
      _=((H).boughtTree.header i).count ∧ ((H).boughtTree.header i).stop≤_
    exact ⟨congrArg PortHeader.owner lastHeader.symm,congrArg PortHeader.parity lastHeader.symm,
      congrArg PortHeader.count lastHeader.symm,endAt⟩

private theorem ends (h : PortHeader) :
    h.owner.base+h.owner.size≤h.stop ∧ h.parity.base+h.parity.size≤h.stop := by
  change h.owner.base+h.large≤h.owner.base+h.large+h.large ∧ _≤_
  exact ⟨Nat.le_add_right ..,le_rfl⟩

theorem paid_economic_bank_ends (a : Attempt) (live : Event.attempt a∈events v.mesh) :
    (fmt a).stockSource.owner.base+(fmt a).stockSource.owner.size≤(G).first ∧
    (fmt a).stockSource.parity.base+(fmt a).stockSource.parity.size≤(G).first ∧
    (tre a).owner.base+(tre a).owner.size≤(G).first ∧
    (tre a).parity.base+(tre a).parity.size≤(G).first := by
  obtain ⟨⟨oo,op,_,oe⟩,⟨treeOwner,tp,_,te⟩⟩:=paid_economic_headers v P z width a live
  rw [oo,op,treeOwner,tp]
  exact ⟨(ends _).1.trans oe,(ends _).2.trans oe,(ends _).1.trans te,(ends _).2.trans te⟩

theorem paid_economic_rows (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
    (flag : ℕ) (m : Memory W) (pub : (H).Resident m)
    (ready : Calendar.mounted (v.nativeChart P z width r banks src tab dst owners) (events v.mesh) m)
    (after : (G).first≤flag) :
    let final:=checkedOut (v.nativeChart P z width r banks src tab dst owners) flag m
    (∀ a,Event.attempt a∈events v.mesh→PaidEventDirectory.Rows (fmt a).stockSource.owner (fmt a).stockSource.parity
      final (fmt a).pricedArea.occurrences) ∧
    (∀ a,Event.attempt a∈events v.mesh→PaidEventDirectory.Rows (tre a).owner (tre a).parity final (tre a).positions) := by
  intro final
  let C:=v.nativeChart P z width r banks src tab dst owners
  have low (x : ℕ) (hx : x<(G).first) : final x=m x := by
    change (checkedOut C flag m) x=_
    rw [checkedOut,ProtocolRAMGeneratedWrite.frame_image flag 1 _ _ x (.inl (hx.trans_le after))]
    apply run_frame C _ m x ready
    intro e _
    exact (v.event_prefix P z width r banks src tab dst owners e x
      (hx.trans_le (Nat.le_add_right (G).first _))).1
  constructor
  · intro a live
    obtain ⟨⟨own,parity,count,stop⟩,_⟩:=paid_economic_headers v P z width a live
    rw [own,parity,count]
    exact PaidEventDirectory.of_loaded _ _ ((pub.ports 0).frame (fun x _ hi=>low x (hi.trans_le stop)))
  · intro a live
    obtain ⟨_,⟨own,parity,count,stop⟩⟩:=paid_economic_headers v P z width a live
    rw [own,parity,count]
    apply PaidEventDirectory.of_loaded
    have loaded : (paidTreeHeader v P z width a live).Loaded m := by
      cases a
      · exact pub.payloadTree _
      · exact pub.boughtTree _
    exact loaded.frame (fun x _ hi=>low x (hi.trans_le stop))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
