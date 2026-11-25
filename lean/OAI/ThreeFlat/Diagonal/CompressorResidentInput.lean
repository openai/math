import OAI.ThreeFlat.Diagonal.CompressorResidentHeader

namespace OAI
/-! # Shrink-step read footprint through graph, key and issued-width sweeps -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.NatCast
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l : ℕ}
variable (S : Graph.Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (b : B ≃ Fin N) (hc : 2≤S.colors) (lay : Bool) (p : Pointers) (cell : Word w)
variable (prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ)

abbrev InSpan (a lo len : ℕ) : Prop := lo≤a ∧ a<lo+len

inductive Read (x : Dimensions) (p : Pointers) (current : ℕ) (a : ℕ) : Prop where
  | current (h : a=current)
  | header (h : InSpan a p.ownHeader 34)
  | graph (h : InSpan a p.oldGraph (6*x.oldEdges))
  | widths (h : InSpan a p.oldWidths (x.oldEdges*x.originalLanes))
  | sliced (h : InSpan a p.split (8*x.oldEdges))
  | colors (h : InSpan a p.colors x.oldBase)
  | offsets (h : InSpan a p.offsets x.oldBase)
  | issued (h : InSpan a p.supply (8*x.motifs))

section
variable (supply : P.Motif → Fin 8 → ℕ)
local notation "x" => dims S N t l
local notation "old" => incoming S N p

structure Input (m : Memory w) : Prop where
  hdr : Header x p lay cell m
  graph : SlotImage.Stored (StageAddress.packedGraph P) b (Demand.laneOrdinal P) old
    (fun i=>(m i).val) (fun e=>prior (packedAddress e))
  aux : StoredColumns.Auxiliary P b old (extra p) m
  widthBound : p.oldWidths+(x).oldEdges*(x).originalLanes≤2^w
  supplyBound : p.supply+8*(x).motifs≤2^w
  issuedRows : ∀ (a : P.Motif) (j : Fin 8),m (p.supply+
    (denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val*8+j.val)=(supply a j:Word w)

variable {S P b hc lay p cell prior supply}
omit [Fintype B] [Fintype H] in
/-- Reopen the persistent operand tables using an independently loaded cursor register. -/
theorem Input.frameWith {m alt : Memory w} (I : Input S P b hc lay p cell prior supply m) (kernel : Word w)
    (pointer : (alt kernel.val).val=p.ownHeader)
    (eq : ∀ a,(∀ address,Read x p address a) → alt a=m a) :
    Input S P b hc lay p kernel prior supply alt := by
  have hdr : Header x p lay kernel alt := by
    refine ⟨pointer,I.hdr.safe,?_⟩
    intro i
    rw [eq _ (fun _=>.header ⟨Nat.le_add_right ..,Nat.add_lt_add_left i.isLt _⟩)]
    exact I.hdr.words i
  have g := I.graph.frame
    (fun a lo hi=>congrArg Fin.val (eq a (fun _=>.graph ⟨lo,hi⟩)))
    (fun a lo hi=>congrArg Fin.val (eq a (fun _=>.widths ⟨lo,hi⟩)))
  refine ⟨hdr,g,?_,I.widthBound,I.supplyBound,?_⟩
  · refine ⟨?_,?_,?_,I.aux.colorFits,I.aux.offsetFits,I.aux.splitFits,I.aux.graphFits⟩
    · intro v
      dsimp only [extra]
      rw [eq _ (fun _=>.colors ⟨Nat.le_add_right ..,Nat.add_lt_add_left (b v).isLt _⟩)]
      exact I.aux.color v
    · intro v
      dsimp only [extra]
      rw [eq _ (fun _=>.offsets ⟨Nat.le_add_right ..,Nat.add_lt_add_left (b v).isLt _⟩)]
      exact I.aux.offset v
    · intro v rev j
      have col : (if rev then 4 else 0)+j.val<8 := by
        cases rev <;> have := j.isLt <;> simp <;> omega
      have mul := Nat.mul_le_mul_left (old).rows col
      rw [Nat.mul_succ] at mul
      have idx : SlotImage.ordinal b v<(old).rows := SlotImage.ordinal_lt b v
      have raw := SlotImage.cell_range I.graph v rev 2
      have inside : InSpan (p.split+(old).rows*((if rev then 4 else 0)+j.val)+SlotImage.ordinal b v)
          p.split (8*(old).rows) := by constructor <;> omega
      dsimp only [extra]
      rw [eq _ (fun _=>.sliced inside),eq _ (fun _=>.graph raw)]
      exact I.aux.split v rev j
  · intro a j
    have row := (denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).isLt
    change (denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val<(x).motifs at row
    have col := j.isLt
    rw [eq _ (fun _=>.issued (by constructor <;> omega))]
    exact I.issuedRows a j

omit [Fintype B] [Fintype H] in
theorem Input.frame {m alt : Memory w} (I : Input S P b hc lay p cell prior supply m)
    (eq : ∀ a,Read x p cell.val a → alt a=m a) :
    Input S P b hc lay p cell prior supply alt :=
  I.frameWith cell (by rw [eq _ (.current rfl)];exact I.hdr.pointer) (fun a h=>eq a (h cell.val))

variable {m : Memory w} (I : Input S P b hc lay p cell prior supply m)
include I
omit [Fintype B] [Fintype H] in
theorem Input.arc (E : Codec B w S.colors t l) (vs : Fin 1 → Word w)
    (number : ∀u,E.base u=((b u).val:Word w))
    (add : ∀u v,slotCode (w:=w) P (u+v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
    (sub : ∀u v,slotCode (w:=w) P (u-v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v)) :
    ArcReads P E (Template.g.map (Formula.value (fun _=>cell) m vs)) m := by
  rw [I.hdr.oldColumns]
  exact StoredColumns.reads P E b old (extra p) m _ I.graph I.aux number add sub

omit [Fintype B] [Fintype H] in
theorem Input.widths (E : Codec B w S.colors t l) (vs : Fin 1 → Word w)
    (number : ∀u,E.base u=((b u).val:Word w)) :
    Demand.WidthReads P E (baseNat b) (fun _=>cell) m vs (Template.f oldWidths) (Template.f tags)
      (Template.f oldLanes) prior :=
  Demand.widths_from_image b E old (fun _=>cell) m vs prior I.graph _ _ _
    (I.hdr.field vs 13) number (I.hdr.field vs 15) (I.hdr.field vs 26) I.widthBound

end

variable {S P b hc lay p cell prior}
omit [Fintype B] [Fintype H] in
theorem Input.supply {supply : P.Motif → Fin 8 → ℕ} {m : Memory w}
    (I : Input S P b hc lay p cell prior supply m) (vs : Fin 1 → Word w) (a : P.Motif) (j : Fin 8) :
    m (Formula.value (fun _=>cell) m vs (Template.f issued)+
      (((denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val:Word w)*8+(j.val:Word w))).val =
      (supply a j:Word w) := by
  let row := (denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val
  have hrow : row<(dims S N t l).motifs := (denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).isLt
  have origin : Formula.value (fun _=>cell) m vs (Template.f issued)=(p.supply:Word w) := I.hdr.field vs 3
  have fit := I.supplyBound
  have col := j.isLt
  have addr : p.supply+row*8+j.val<2^w := by omega
  have convert : (p.supply:Word w)+((row:Word w)*8+(j.val:Word w)) =
      ((p.supply+row*8+j.val:ℕ):Word w) := by
    have mul : (row:Word w)*8=((row*8:ℕ):Word w) := by
      apply Fin.ext
      exact (Nat.mul_mod row 8 (2^w)).symm
    rw [mul,←Nat.cast_add,←Nat.cast_add,Nat.add_assoc]
  rw [origin,convert,Fin.val_cast_of_lt addr]
  exact I.issuedRows a j


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
