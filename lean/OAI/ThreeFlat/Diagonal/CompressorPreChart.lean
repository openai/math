import OAI.ThreeFlat.Diagonal.CompressorGreedyImage
import OAI.ThreeFlat.Diagonal.CompressorDemandAdmission

namespace OAI
/-! # Old-width addressing and typed demands after the canonical prepass coloring -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.NatCast
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l : ℕ}
variable (S : Graph.Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (b : B ≃ Fin N) (p : Pointers) (cell : Word w)
variable (prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ)
local notation "C" => incoming S N p
local notation "x" => dims S N t l

structure Chart (m : Memory w) : Prop extends Old S P b p cell prior m where
  aux : StoredColumns.Auxiliary P b C (extra p) m
  widthsFit : p.oldWidths+(x).oldEdges*(x).originalLanes≤2^w

variable {S P b p cell prior} {m alt : Memory w}
omit [Fintype B] [Fintype H] [AddCommGroup H] in
theorem Chart.demandFrame (q : Chart S P b p cell prior m) (s : Fresh (dims S N t l) p cell.val)
    (frame : agreesOutside p.demands (p.demands+2*(x).motifs) alt m) : Chart S P b p cell prior alt := by
  have lower:=s.demandEnd
  have mid:=s.splitEnd
  have color:=s.colorEnd
  have upper:=s.offsetEnd
  have old:=q.toOld.frame s (smallerFrame s le_rfl (by omega) frame)
  refine ⟨old,?_,q.widthsFit⟩
  refine ⟨?_,?_,?_,q.aux.colorFits,q.aux.offsetFits,q.aux.splitFits,q.aux.graphFits⟩
  · intro v
    rw [frame _ (.inr (by change _≤p.colors+_;omega))]
    exact q.aux.color v
  · intro v
    rw [frame _ (.inr (by change _≤p.offsets+_;omega))]
    exact q.aux.offset v
  · intro u rev j
    have raw:=(SlotImage.cell_range q.stored u rev 2).2.trans_le s.oldGraph
    rw [frame _ (.inr (by change _≤p.split+_+_;omega)),frame _ (.inl raw)]
    exact q.aux.split u rev j

variable (q : Chart S P b p cell prior m) (E : Codec B w S.colors t l)
variable (code : ∀v,E.base v=((b v).val:Word w))
variable (add : ∀u v,slotCode (w:=w) P (u+v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
variable (sub : ∀u v,slotCode (w:=w) P (u-v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
include q code add sub in
omit [Fintype B] [Fintype H] in
theorem Chart.arcs (vs : Fin 1→Word w) :
    ArcReads P E (Template.g.map (Formula.value (fun _=>cell) m vs)) m := by
  rw [q.header.oldColumns]
  exact StoredColumns.reads P E b C (extra p) m _ q.stored q.aux code add sub

include q code in
omit [Fintype B] [Fintype H] [AddCommGroup H] in
theorem Chart.widths (vs : Fin 1→Word w) :
    Demand.WidthReads P E (baseNat b) (fun _=>cell) m vs (Template.f oldWidths) (Template.f tags)
      (Template.f oldLanes) prior :=
  Demand.widths_from_image b E C (fun _=>cell) m vs prior q.stored _ _ _
    (q.header.field vs 13) code (q.header.field vs 15) (q.header.field vs 26) q.widthsFit

include q in
omit [Fintype B] [Fintype H] in
theorem Chart.supply {lay : Bool} {hc : 2≤S.colors} {supply : P.Motif → Fin 8 → ℕ}
    (hdr : Header (dims S N t l) p lay cell m) (sBound : p.supply+8*(x).motifs≤2^w)
    (row : ∀ a j,m (p.supply+(denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val*8+j.val)=(supply a j:Word w)) :
    Input S P b hc lay p cell prior supply m :=
  ⟨hdr,q.stored,q.aux,q.widthsFit,sBound,row⟩


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
