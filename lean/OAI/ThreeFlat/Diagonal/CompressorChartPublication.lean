import OAI.ThreeFlat.Diagonal.CompressorPreChart

namespace OAI
/-! # Carrying the old physical chart across histogram and chosen-layout publication -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan
open scoped Fin.NatCast
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l : ℕ}
variable {S : Graph.Stage} {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {b : B ≃ Fin N} {p : Pointers} {cell : Word w} {m z : Memory w}
variable {hc : 2≤S.colors} {lay : Bool}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ} {supply : P.Motif → Fin 8→ℕ}
local notation "x" => dims S N t l
local notation "C" => incoming S N p

inductive ChartRead (shape : Dimensions) (p : Pointers) (a : ℕ) : Prop where
  | graph (h : InSpan a p.oldGraph (6*shape.oldEdges))
  | widths (h : InSpan a p.oldWidths (shape.oldEdges*shape.originalLanes))
  | aux (h : p.split≤a ∧ a<p.newGraph)

omit [Fintype B] [Fintype H] in
theorem Chart.publish (q : Chart S P b p cell prior m) (s : Fresh (dims S N t l) p cell.val)
    (hdr : Header (dims S N t l) p lay cell z) (supFits : p.supply+8*(x).motifs≤2^w)
    (issued : ∀a j,z (p.supply+(denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val*8+j.val)=(supply a j:Word w))
    (saved : ∀a,ChartRead x p a → z a=m a) : Input S P b hc lay p cell prior supply z := by
  have old := q.stored.frame (fun a lo hi=>congrArg Fin.val (saved a (.graph ⟨lo,hi⟩)))
    (fun a lo hi=>congrArg Fin.val (saved a (.widths ⟨lo,hi⟩)))
  have s1:=s.splitEnd
  have s2:=s.colorEnd
  have s3:=s.offsetEnd
  have baseCount : (dims S N t l).oldBase = N := rfl
  have edgeCount : (dims S N t l).oldEdges = (C).rows := rfl
  refine ⟨hdr,old,?_,q.widthsFit,supFits,issued⟩
  refine ⟨?_,?_,?_,q.aux.colorFits,q.aux.offsetFits,q.aux.splitFits,q.aux.graphFits⟩
  · intro v
    have idx:=(b v).isLt
    rw [saved _ (.aux (by change p.split≤p.colors+_ ∧ p.colors+_<p.newGraph;constructor <;> omega))]
    exact q.aux.color v
  · intro v
    have idx:=(b v).isLt
    rw [saved _ (.aux (by change p.split≤p.offsets+_ ∧ p.offsets+_<p.newGraph;constructor <;> omega))]
    exact q.aux.offset v
  · intro v rev j
    have col : (if rev then 4 else 0)+j.val<8 := by cases rev <;> have:=j.isLt <;> simp <;> omega
    have mul:=Nat.mul_le_mul_left (C).rows col
    rw [Nat.mul_succ] at mul
    have idx : SlotImage.ordinal b v<(C).rows:=SlotImage.ordinal_lt b v
    have raw:=SlotImage.cell_range q.stored v rev 2
    have inside : ChartRead x p (p.split+(C).rows*((if rev then 4 else 0)+j.val)+SlotImage.ordinal b v) := by
      apply ChartRead.aux
      constructor <;> omega
    change (z (p.split+(C).rows*((if rev then 4 else 0)+j.val)+SlotImage.ordinal b v)).val =
      StoredColumns.digit S.colors S.degree t j.val (z (SlotImage.cell C b v rev 2)).val
    rw [saved _ inside,saved _ (.graph raw)]
    exact q.aux.split v rev j


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
