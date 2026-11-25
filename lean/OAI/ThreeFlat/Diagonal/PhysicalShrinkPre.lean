import OAI.ThreeFlat.Diagonal.PhysicalShrinkImage
import OAI.ThreeFlat.Diagonal.CompressorPreImage
import OAI.ThreeFlat.Diagonal.ShrinkRowScan

namespace OAI
/-! # Computing the native shrinking move's old chart and paired demands -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorScan Computability.VPVNP.Compression
open CompressorPacking Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement
open NavigationDirectory NavigationPass PhysicalShrink
open scoped Classical Fin.NatCast
noncomputable section
private theorem palette_two (degree : ℕ) : 2≤2*(2^degree)+1 := by
  have := Nat.two_pow_pos degree
  omega

variable (s D rem : ℕ) (A : State (2^s) (shrinkCharge s+rem))
local notation "P" => shrinkRecordPacking s rem A
local notation "ord" => shrinkRecordOrder s rem A
local notation "N" => Fintype.card (State.Base (shrinkRecordState s rem A))
local notation "d" => (2^s : ℕ)
local notation "k" => (2*d+1 : ℕ)
local notation "S" => shrinkStage s D
local notation "x" => dims S N (tagBits d) rem
local notation "hc" => palette_two s
local notation "prior" => shrinkRecordWidth s rem A
local notation "du" => PhysicalShrink.b P prior (shrinkRecordCode s rem A) hc
variable {W K : ℕ} (cur : Word W) (m : Memory W) (c : Cursor)
local notation "p" => pointers K c x
local notation "C" => incoming S N p

structure ShrinkOldCaps (s rem W : ℕ) : Prop where
  eight : 8<2^W
  colors : 2^(2*(2^s)+1)<2^W
  slots : 2^s<2^W
  tags : 2^(tagBits (2^s))<2^W
  residual : 2^rem<2^W
  bundle : 3*(2^(2*(2^s)+1)*2^s)/4<2^W

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem native_shrink_old (space : CursorSpace cur m c K x)
    (stored : SlotImage.Stored A.graph A.order (tagOrdinal _) C (fun i=>(m i).val) A.width)
    (caps : ShrinkOldCaps s rem W) (totals : ∀a:(P).Motif,thickWidth P prior ((P).bundle a)<2^W) :
    let E:=shrinkOld cur s D
    let out:=(E.run m).2
    E.fits m ∧ agreesOutside (p).demands (p).newGraph out m ∧
      Chart S P (shrinkRecordState s rem A).order p cur prior out ∧
      ∀(a : (P).Motif) (j : Fin 2),out ((p).demands+2*(ord a).val+j.val)=(du a j:Word W) := by
  let : DecidableEq (State.Base (shrinkRecordState s rem A)) := Classical.decEq _
  let b:=(shrinkRecordState s rem A).order
  have cap (i : ℕ) (h : 2^i<2^W) : i≤W :=
    ((Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp h).le
  let E : Codec (shrinkRecordState s rem A).Base W k (tagBits d) rem :=
    ⟨fun v=>((b v).val:Word W),cap k caps.colors,cap _ caps.tags,cap _ caps.residual⟩
  have chart (z : BitWord s) : slotCode (w:=W) P z=tagWord (cap _ caps.slots) z :=
    Demand.tag_cast (cap _ caps.slots) z
  have add (u v : BitWord s) : slotCode (w:=W) P (u+v) =
      BinaryOp.bitXor.eval (slotCode P u) (slotCode P v) :=
    (chart _).trans ((tagWord_add (cap _ caps.slots) u v).trans
      (congrArg₂ BinaryOp.bitXor.eval (chart u).symm (chart v).symm))
  have sub (u v : BitWord s) : slotCode (w:=W) P (u-v) =
      BinaryOp.bitXor.eval (slotCode P u) (slotCode P v) :=
    (chart _).trans ((tagWord_sub (cap _ caps.slots) u v).trans
      (congrArg₂ BinaryOp.bitXor.eval (chart u).symm (chart v).symm))
  have first : Old S P b p cur prior m := ⟨space.pristine,shrinkImage s rem A C _ stored,by
    have f:=space.fresh
    have:=f.oldGraph;have:=f.demandEnd;have:=f.splitEnd;have:=f.colorEnd;have:=f.offsetEnd
    have:=f.high;have:=cur.isLt;omega⟩
  have one : (1:Word W)≠0 := by
    intro eqv
    have same:=congrArg Fin.val eqv
    have lt : 1 < 2^W := by have := caps.eight; omega
    have unit : (1 : Word W).val = 1 := Fin.val_cast_of_lt lt
    change (1 : Word W).val = 0 at same
    omega
  exact first.pre_image space.fresh (fun _=>0) hc ((@Nat.lt_two_pow_self k).le.trans caps.colors.le)
    (cap _ caps.tags) caps.eight one (fun _=>rfl) (fun _=>rfl)
    caps.colors ⟨caps.slots,caps.tags,caps.residual⟩ E (fun _=>rfl)
    add sub caps.bundle totals

theorem shrink_cursor_frame (space : CursorSpace cur m c K x) (alt : Memory W)
    (frame : agreesOutside (p).demands (p).newGraph alt m) : CursorSpace cur alt c K x := by
  have f:=space.fresh
  refine ⟨⟨?_,space.header.fit,?_⟩,space.graph,space.widths,space.counts,space.earlier,space.controls⟩
  · rw [frame _ (.inr f.high)]; exact space.header.pointer
  · intro i hi
    rw [frame _ (.inl (by have:=f.header;change c.header+64≤(p).demands at this;omega))]
    exact space.header.values i hi


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
