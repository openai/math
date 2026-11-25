import OAI.ThreeFlat.Diagonal.CompressorGreedySweep
import OAI.ThreeFlat.Diagonal.CompressorOffsetTemplate
import OAI.ThreeFlat.Diagonal.ShrinkCursorLayout

namespace OAI
/-! # Four old immutable column reads used by the in-place binary coloring and offset scans -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.PhysicalPinsExpr Placement
open scoped Fin.NatCast
variable {B H : Type} [AddCommGroup H] {w N t l : ℕ}
variable (S : Graph.Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (b : B ≃ Fin N) (p : Pointers) (cell : Word w)
variable (prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ)
set_option quotPrecheck false
local notation "C" => incoming S N p
local notation "x" => dims S N t l

structure Old (m : Memory w) : Prop where
  header : Header x p false cell m
  stored : SlotImage.Stored (StageAddress.packedGraph P) b (Demand.laneOrdinal P) C
    (fun i=>(m i).val) (fun e=>prior (packedAddress e))
  graphFits : p.oldGraph+6*(x).oldEdges≤2^w

structure Sliced (m : Memory w) : Prop extends Old S P b p cell prior m where
  splitFits : p.split+8*(x).oldEdges≤2^w
  split : ∀ (v : B × Fin S.degree) (back : Bool) (j : Fin 4),
    (m (p.split+(C).rows*((if back then 4 else 0)+j.val)+SlotImage.ordinal b v)).val =
      StoredColumns.digit S.colors S.degree t j.val (m (SlotImage.cell C b v back 2)).val

variable {S P b p cell prior} {m : Memory w}
variable (pub : Fin 1→Word w) (vs : Fin 1→Word w)

private theorem row_word (base a d i : ℕ) :
    (base : Word w)+(a : Word w)*(d : Word w)+(i : Word w) =
      ((base+(a*d+i) : ℕ) : Word w) := by
  have product : (a : Word w)*(d : Word w)=((a*d : ℕ) : Word w) :=
    Fin.ext (Nat.mul_mod a d (2^w)).symm
  rw [product, Nat.cast_add base, Nat.cast_add (a*d), add_assoc]

omit [AddCommGroup H] in
theorem Old.neighbor (h : Old S P b p cell prior m) (rev : Bool) (v : B) (i : Fin S.degree) :
    let g:=(if rev then Template.g.src else Template.g.dst)
    m ((Template.emit cell g).eval pub m vs+((b v).val:Word w)*(S.degree:Word w)+(i.val:Word w)).val=
      ((b ((if rev then P.slots.target.symm else P.slots.target) (v,i)).1).val:Word w) := by
  have q:=(h.header.oldColumns vs)
  have field : Formula.value (fun _=>cell) m vs (if rev then Template.g.src else Template.g.dst)=
      ((p.oldGraph+(C).rows*SlotImage.column rev 0:ℕ):Word w) := by
    cases rev with
    | false => exact congrArg (fun a : ArcColumns (Word w)=>a.dst) q
    | true => exact congrArg (fun a : ArcColumns (Word w)=>a.src) q
  let dir:=SlotImage.column rev 0
  have j : dir<6 := by cases rev <;> decide
  have row : SlotImage.ordinal b (v,i)<(C).rows := SlotImage.ordinal_lt b (v,i)
  have mul:=Nat.mul_le_mul_left (C).rows j
  rw [Nat.mul_succ] at mul
  have bound : p.oldGraph+6*(C).rows≤2^w := h.graphFits
  have idx : p.oldGraph+(C).rows*dir+SlotImage.ordinal b (v,i)<2^w := by omega
  dsimp only
  rw [Template.program_value,field]
  have address : ((p.oldGraph+(C).rows*dir:ℕ):Word w)+((b v).val:Word w)*(S.degree:Word w)+(i.val:Word w)=
      ((p.oldGraph+(C).rows*dir+SlotImage.ordinal b (v,i):ℕ):Word w) := by
    exact row_word _ _ _ _
  rw [address,Fin.val_cast_of_lt idx]
  cases rev <;> exact (Fin.cast_val_eq_self _).symm.trans (congrArg Nat.cast (h.stored.neighbor (v,i) _))

omit [AddCommGroup H] in
theorem Sliced.tag (h : Sliced S P b p cell prior m) (tw : t≤w) (rev : Bool) (v : B) (i : Fin S.degree) :
    let g:=(if rev then Template.g.backTag else Template.g.forwardTag)
    m ((Template.emit cell g).eval pub m vs+((b v).val:Word w)*(S.degree:Word w)+(i.val:Word w)).val=
      tagWord tw (P.siteShift (if rev then P.slots.target.symm (v,i) else (v,i))).1 := by
  let dir:=(if rev then 4 else 0)+2
  have q:=(h.header.oldColumns vs)
  have field : Formula.value (fun _=>cell) m vs (if rev then Template.g.backTag else Template.g.forwardTag)=
      ((p.split+(C).rows*dir:ℕ):Word w) := by
    cases rev with
    | false => exact congrArg (fun a : ArcColumns (Word w)=>a.forwardTag) q
    | true => exact congrArg (fun a : ArcColumns (Word w)=>a.backTag) q
  have j : dir<8 := by cases rev <;> decide
  have row : SlotImage.ordinal b (v,i)<(C).rows := SlotImage.ordinal_lt b (v,i)
  have mul:=Nat.mul_le_mul_left (C).rows j
  rw [Nat.mul_succ] at mul
  have bound : p.split+8*(C).rows≤2^w := h.splitFits
  have idx : p.split+(C).rows*dir+SlotImage.ordinal b (v,i)<2^w := by omega
  dsimp only
  rw [Template.program_value,field]
  have address : ((p.split+(C).rows*dir:ℕ):Word w)+((b v).val:Word w)*(S.degree:Word w)+(i.val:Word w)=
      ((p.split+(C).rows*dir+SlotImage.ordinal b (v,i):ℕ):Word w) := by
    exact row_word _ _ _ _
  rw [address,Fin.val_cast_of_lt idx]
  apply Fin.ext
  exact (h.split (v,i) rev 2).trans
    (StoredColumns.stored_slice P b C _ _ h.stored (v,i) rev 2)


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
