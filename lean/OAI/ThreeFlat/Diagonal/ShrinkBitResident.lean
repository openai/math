import OAI.ThreeFlat.Diagonal.ShrinkBitLookup
import OAI.ThreeFlat.Diagonal.CompressorResidentInput
import OAI.ThreeFlat.Diagonal.CompressorSupplyPhysicalRead

namespace OAI
/-! # Relocating a live shrink stage to an occupied site's geometry registers -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.NatCast
namespace Resident
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l n : ℕ}
variable {S : Graph.Stage} {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {b : B≃Fin N} {hc : 2≤S.colors} {lay : Bool} {p : Pointers} {cell : Word w}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors→ℕ} {issued : P.Motif→Fin 8→ℕ}
variable {mem : Memory w} {data : Param→Word w} {vs : Fin n→Word w} (ptr : Formula n)
set_option quotPrecheck false
local notation "V" => Formula.value data mem vs
local notation "o" => Demand.formulaOps n
local notation "f" => atField o ptr
local notation "g" => oldColumns o ptr
local notation "X" => dims S N t l

/-- Persistent bytes read by a selected party. The transient navigation cursor
and the node-preparation scratch arenas have no entry in this relation. -/
inductive GeometryRead (x : Dimensions) (p : Pointers) (a : ℕ) : Prop where
  | old (read : ∀ address,Read x p address a)
  | graph (span : InSpan a p.newGraph (6*x.newEdges))
  | keys (span : InSpan a p.keys x.newEdges)
  | width (span : InSpan a p.newWidths (x.newEdges*x.residual))

def GeometryFrame (x : Dimensions) (p : Pointers) (original later : Memory w) :=
  ∀ a,GeometryRead x p a → later a=original a

theorem GeometryFrame.refl (m : Memory w) : GeometryFrame X p m m := fun _ _=>rfl

theorem GeometryFrame.trans {m₁ m₂ m₃ : Memory w} (first : GeometryFrame X p m₁ m₂)
    (last : GeometryFrame X p m₂ m₃) : GeometryFrame X p m₁ m₃ :=
  fun a h=>(last a h).trans (first a h)

omit [Fintype B] [Fintype H] in
theorem Input.relocate (I : Input S P b hc lay p cell prior issued mem) (kernel : Word w)
    (stage : (mem kernel.val).val=p.ownHeader) : Input S P b hc lay p kernel prior issued mem :=
  ⟨⟨stage,I.hdr.safe,I.hdr.words⟩,I.graph,I.aux,I.widthBound,I.supplyBound,I.issuedRows⟩

theorem Header.viewField {dim : Dimensions} (h : Header dim p lay cell mem)
    (atCell : V ptr=cell) (i : Fin 34) : V (f i.val)=(value dim p lay i.val:Word w) := by
  change mem (mem (V ptr).val+(i.val:Word w)).val=_
  rw [atCell];exact h.native i

theorem Header.viewColumns (h : Header X p lay cell mem) (atCell : V ptr=cell) :
    (g).map V=StoredColumns.addresses (incoming S N p) (extra p) := by
  have same : (g).map V=Template.g.map (Formula.value (fun _=>cell) mem (fun _=>0)) := by
    simp [ShrinkStage.oldColumns,ArcColumns.map,Columns.map,column,atField,Demand.formulaOps,Formula.value,
      Template.g,Template.ptr,atCell]
  rw [same];exact h.oldColumns _

variable (I : Input S P b hc lay p cell prior issued mem)
variable (E : Codec B w S.colors t l) (atCell : Formula.value data mem vs ptr=cell)
variable (num : ∀u,E.base u=((b u).val:Word w))
variable (add : ∀u v,slotCode (w:=w) P (u+v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
variable (sub : ∀u v,slotCode (w:=w) P (u-v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))

include I atCell num add sub in
omit [Fintype B] [Fintype H] in
theorem Input.viewArc : ArcReads P E ((oldColumns (Demand.formulaOps n) ptr).map (Formula.value data mem vs)) mem := by
  rw [I.hdr.viewColumns ptr atCell]
  exact StoredColumns.reads P E b _ _ mem _ I.graph I.aux num add sub

include I atCell num in
omit [Fintype B] [Fintype H] in
theorem Input.viewWidths : Demand.WidthReads P E (baseNat b) data mem vs (f oldWidths) (f tags) (f oldLanes) prior :=
  Demand.widths_from_image b E _ data mem vs prior I.graph _ _ _
    (I.hdr.viewField ptr atCell 13) num (I.hdr.viewField ptr atCell 15) (I.hdr.viewField ptr atCell 26) I.widthBound

include I atCell num add sub in
omit [Fintype B] [Fintype H] in
theorem Input.viewOldArc (a : P.Motif) (incident : Formula n)
    (row : mem (V incident).val=(Demand.key P (baseNat b) a.val:Word w))
    (size : S.degree<2^w ∧ 2^t<2^w ∧ 2^l<2^w) (colors : 2^S.colors<2^w) :
    (BitOrigins.oldArc ptr S (.load incident)).map V=encodeEnds P E a.val := by
  have Wd:=I.viewWidths (data:=data) (vs:=vs) ptr E atCell num
  exact BitOrigins.arc_read S P E b ptr data mem vs (I.viewArc ptr E atCell num add sub) num
    (I.hdr.viewField ptr atCell 15) (I.hdr.viewField ptr atCell 14) size colors a.val _ row (Wd.ordinalFits a.val)

open scoped Fin.CommRing in
private theorem supply_address {width : ℕ} (base row col : ℕ) :
    (base:Word width)+((row:Word width)*8+(col:Word width))=((base+row*8+col:ℕ):Word width) := by
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,add_assoc]

include I atCell in
omit [Fintype B] [Fintype H] in
theorem Input.viewSupply (m : P.Motif) (i : Fin 8) :
    mem (V (f ShrinkStage.issued)+
      (((denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc m).val:Word w)*8+(i.val:Word w))).val =
      (issued m i:Word w) := by
  let row:=(denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc m).val
  have rr : row<(X).motifs := (denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc m).isLt
  have cap:=I.supplyBound
  have off:=i.isLt
  have addr : p.supply+row*8+i.val<2^w := by omega
  have origin : V (f ShrinkStage.issued)=(p.supply:Word w) := I.hdr.viewField ptr atCell 3
  change mem (V (f ShrinkStage.issued)+((row:Word w)*8+(i.val:Word w))).val=_
  rw [origin,supply_address p.supply row i.val,Fin.val_cast_of_lt addr]
  exact I.issuedRows m i

include I atCell num add sub in
/-- Source and target graph reads for the chosen stage in the selected node's
register frame, including the actual monotonically numbered source key file. -/
def Input.supplyFiles {pad : ℕ} (bound : ∀k,S.pieces k≤S.pieceRadix)
    (graph : LiftedSlots (B × BitWord t) (Graph.liveDegree S+pad) (BitWord l))
    (width : SlotImage.Edge (B × BitWord t) (BitWord l) (Graph.liveDegree S+pad)→ℕ)
    (saved : SlotImage.Stored graph (Template.tagNumber b) (tagOrdinal l) (outgoing S N t p)
      (fun j=>(mem j).val) width)
    (keysRead : ∀u : (B × BitWord t) × Fin (Graph.liveDegree S+pad),
      mem (p.keys+SlotImage.ordinal (Template.tagNumber b) u)=
      (Template.sourceKey (n:=pad) S P b bound lay hc u:Word w))
    (keyFit : ∀q,Graph.edgeId S P (baseNat b) bound q<2^w)
    (keyRoom : p.keys+(outgoing S N t p).rows≤2^w)
    (graphRoom : p.newGraph+6*(outgoing S N t p).rows≤2^w)
    (live : S.liveDegree=Graph.liveDegree S) (full : S.outputDegree=Graph.liveDegree S+pad) :
    BitOrigins.SupplyFiles S P E b bound lay hc ptr data mem vs prior issued pad := by
  refine ⟨graph,outgoing S N t p,width,p.keys,I.viewArc ptr E atCell num add sub,I.viewWidths ptr E atCell num,
    ?_,I.viewSupply ptr atCell,saved,keysRead,keyFit,keyRoom,graphRoom,live,full,
    I.hdr.viewField ptr atCell 23,I.hdr.viewField ptr atCell 20,I.hdr.viewField ptr atCell 22⟩
  unfold radices Radices.map
  rw [show V (f tags)=((2^t:ℕ):Word w) from I.hdr.viewField ptr atCell 15,
    show V (f remaining)=((2^l:ℕ):Word w) from I.hdr.viewField ptr atCell 14]
  rfl


end Resident
end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
