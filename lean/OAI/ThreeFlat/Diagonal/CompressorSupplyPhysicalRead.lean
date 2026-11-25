import OAI.ThreeFlat.Diagonal.CompressorSupplyCrossRead
import OAI.ThreeFlat.Diagonal.CompressorRetainedWidth

namespace OAI
/-! # The four-word origin of an actual issued bit in an incident motif -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM.PhysicalPinsExpr Placement Graph
open scoped Fin.NatCast Classical

variable {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H] {W n N t l : ℕ}
variable (S : Graph.Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (E : Codec B W S.colors t l) (b : B ≃ Fin N) (bound : ∀k,S.pieces k≤S.pieceRadix) (lay : Bool) (hc : 2≤S.colors)
variable (ptr : F n) (data : Param → Word W) (mem : Memory W) (vs : Fin n → Word W)
local notation "V" => Formula.value data mem vs
local notation "f" => atField (Demand.formulaOps n) ptr
local notation "g" => oldColumns (Demand.formulaOps n) ptr
local notation "tagged" => Template.tagNumber (t:=t) b
variable (prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors→ℕ) (supply : P.Motif→Fin 8→ℕ)

structure SupplyFiles (pad : ℕ) where
  graph : LiftedSlots (B × BitWord t) (Graph.liveDegree S+pad) (BitWord l)
  cols : SlotImage.Columns
  width : SlotImage.Edge (B × BitWord t) (BitWord l) (Graph.liveDegree S+pad)→ℕ
  keyBase : ℕ
  arcs : ArcReads P E ((oldColumns (Demand.formulaOps n) ptr).map (Formula.value data mem vs)) mem
  oldWidth : Demand.WidthReads P E (baseNat b) data mem vs (f oldWidths) (f tags) (f oldLanes) prior
  rad : (radices (Demand.formulaOps n) ptr S).map V=rowRadices (w:=W) (t:=t) (l:=l) S
  issuedWords : ∀m i,mem (V (f issued)+
    (((denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc m).val:Word W)*8+((i:Fin 8).val:Word W))).val =
    (supply m i:Word W)
  saved : SlotImage.Stored graph tagged (tagOrdinal l) cols (fun j=>(mem j).val) width
  keysRead : ∀u : (B × BitWord t) × Fin (Graph.liveDegree S+pad),mem (keyBase+SlotImage.ordinal tagged u)=(Template.sourceKey S P b bound lay hc u:Word W)
  keyFit : ∀q,edgeId S P (baseNat b) bound q<2^W
  keyRoom : keyBase+cols.rows≤2^W
  graphRoom : cols.graph+6*cols.rows≤2^W
  live : S.liveDegree=Graph.liveDegree S
  full : S.outputDegree=Graph.liveDegree S+pad
  keysField : V (f keys)=(keyBase:Word W)
  graphField : V (f nextGraph)=(cols.graph:Word W)
  rowsField : V (f nextSlots)=(cols.rows:Word W)

variable {S P E b bound lay hc ptr data mem vs prior supply} {pad : ℕ}
variable (files : SupplyFiles S P E b bound lay hc ptr data mem vs prior supply pad)

include files in
theorem SupplyFiles.issued_word (bits : 2^S.colors<2^W) (m : P.Motif) (e : Ends (F n))
    (enc : e.map V=encodeEnds P E m.val) (edge : F n) (i : Fin 8) (read : V edge=(i.val:Word W)) :
    V (supplyWidth ptr S e edge)=(supply m i:Word W) := by
  have src : e.source.map V=posCode P E (sourcePosition m.val) := congrArg Ends.source enc
  have port : V e.originalSlot=(m.val.1.2.val:Word W) := congrArg Ends.originalSlot enc
  have row:=ShrinkWidth.motifRow_code files.arcs files.oldWidth hc bits e.source e.originalSlot m src port
  change V (ShrinkWidth.motifRow g (layout ptr S) e.source e.originalSlot)=_ at row
  change mem (V (f issued)+(V (ShrinkWidth.motifRow g (layout ptr S) e.source e.originalSlot)*8+V edge)).val=_
  rw [row,read,files.issuedWords]

theorem supply_zero_copies (e : Ends (F n)) (party edge j : F n)
    (kind : Fin 4) (no : S.pieces kind=0) (u : Fin 6) (h8 : 8≤2^W)
    (he : V edge=((ShrinkMotif.survivor lay kind).val:Word W)) (hp : V party=(u.val:Word W))
    (hit : u=ShrinkMotif.supplySrc (ShrinkMotif.survivor lay kind) ∨ u=ShrinkMotif.supplyDst (ShrinkMotif.survivor lay kind))
    (col : Fin 4) : V (supplyAddress ptr S lay e party edge j col)=0 := by
  rw [supply_survivor data mem vs _ _ _ _ _ _ _ _ u h8 he hp hit]
  have clear : List.finRange (S.pieces kind)=[] := List.eq_nil_of_length_eq_zero (by simpa using no)
  simp [supplyCopies,clear,locate,empty,Formula.value]

/-- A positive-width retained query lands on the outgoing port of the numbered
copy, or on its actual mate in the successor's stored forward column. -/
theorem SupplyFiles.retained_word (m : P.Motif) (e : Ends (F n)) (enc : e.map V=encodeEnds P E m.val)
    (party edge j : F n) (kind : Fin 4) (u : Fin 6) (col : Fin 4) (h8 : 8≤2^W)
    (bits : 2^S.colors<2^W) (counts : S.pieces kind<2^W) (nonempty : 0<S.pieces kind)
    (hb : supply m (ShrinkMotif.survivor lay kind)<2^W)
    (index : Fin (supply m (ShrinkMotif.survivor lay kind)))
    (he : V edge=((ShrinkMotif.survivor lay kind).val:Word W)) (hp : V party=(u.val:Word W))
    (hj : V j=(index.val:Word W))
    (hit : u=ShrinkMotif.supplySrc (ShrinkMotif.survivor lay kind) ∨ u=ShrinkMotif.supplyDst (ShrinkMotif.survivor lay kind)) :
    let i:=ShrinkMotif.survivor lay kind
    let part:=(SlotEnergy.pieceIndex (supply m i) (S.pieces kind) nonempty).symm index
    let z : ShrinkEdge P S.pieces:=⟨kind,normalize P m,part.1⟩
    let slot:=CompressorRefresh.leftRow (b:=pad) ((ordinalOf S P (baseNat b) bound lay false hc) z)
    let half:=if u=ShrinkMotif.supplySrc i then slot.2.val else
      S.outputDegree+(SlotImage.oriented files.graph false slot).2.val
    V (supplyAddress ptr S lay e party edge j col)=(![2,0,(half:Word W),(part.2.val:Word W)] : Fin 4→Word W) col := by
  let i:=ShrinkMotif.survivor lay kind
  let cut:=SlotEnergy.pieceIndex (supply m i) (S.pieces kind) nonempty
  let part:=cut.symm index
  let z : ShrinkEdge P S.pieces:=⟨kind,normalize P m,part.1⟩
  have ij : (V j).val=(cut ⟨part.1,part.2⟩).val := by
    rw [hj,Fin.val_cast_of_lt (index.isLt.trans hb)]
    exact (congrArg Fin.val (cut.apply_symm_apply index)).symm
  have value:=files.issued_word bits m e enc edge i he
  rw [supply_survivor data mem vs _ _ _ _ _ _ _ _ u h8 he hp hit,
    supply_copy_word data mem vs ptr S lay e party _ j kind part.1 (supply m i) part.2 hb counts value ij]
  obtain ⟨baseWord,keyWord⟩:=crossing_identifiers S P E b ptr data mem vs files.arcs files.oldWidth.baseWord
    bound files.rad lay hc m e enc kind part.1
  obtain ⟨outPort,matePort⟩:=crossing_slot_words data mem vs S P b bound lay hc ptr e kind part.1 z
    files.graph files.cols files.width files.saved files.keyBase files.keysRead files.keyFit files.keyRoom files.graphRoom
    files.live files.full files.keysField files.graphField files.rowsField baseWord keyWord
  exact crossing_party_word data mem vs ptr S lay e party (.lit part.2.val) kind part.1 u h8 _ _ outPort matePort hp col


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
