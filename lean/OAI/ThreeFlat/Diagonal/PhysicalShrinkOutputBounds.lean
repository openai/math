import OAI.ThreeFlat.Diagonal.PhysicalShrinkPre
import OAI.ThreeFlat.Diagonal.CompressorOutputCaps

namespace OAI
/-! # The bounds for the graph, key and width rows of a binary shrinking move -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression
open CompressorPacking Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement Native.Graph
open NavigationPass PhysicalShrink
open scoped Classical Fin.NatCast BigOperators
noncomputable section

/-- Each entry is a bound on a scalar determined by the public stage dimensions. -/
structure ShrinkOutputCaps (s D N W : ℕ) : Prop where
  keys : Resident.keyBound (shrinkStage s D) N (tagBits (2^s))<2^W
  bases : N*2^(tagBits (2^s))≤2^W
  degree : D<2^W
  pieces : (shrinkStage s D).pieceRadix<2^W


private theorem exponent_le {i W : ℕ} (h : 2^i<2^W) : i≤W :=
  ((Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp h).le

def shrinkOutputCodec (s rem : ℕ) (A : State (2^s) (shrinkCharge s+rem)) {W : ℕ}
    (old : ShrinkOldCaps s rem W) :
    Codec (shrinkRecordState s rem A).Base W (2*(2^s)+1) (tagBits (2^s)) rem :=
  ⟨fun v=>(((shrinkRecordState s rem A).order v).val : Word W),
   exponent_le old.colors, exponent_le old.tags, exponent_le old.residual⟩

theorem shrinkPieceBound (s D : ℕ) (i : Fin 4) :
    (shrinkStage s D).pieces i ≤ (shrinkStage s D).pieceRadix :=
  Finset.single_le_sum (fun j _=>Nat.zero_le ((shrinkStage s D).pieces j)) (Finset.mem_univ i)

theorem shrink_output_degree (s D : ℕ) (hD : 0<D) :
    Graph.liveDegree (shrinkStage s D) + PhysicalShrink.padding (2*(2^s)+1) (2^s) D = D :=
  PhysicalShrink.degree_eq (c:=2*(2^s)+1) (d:=2^s) (D:=D)
    (by have:=Nat.two_pow_pos s; omega) (Nat.two_pow_pos s) hD

set_option maxHeartbeats 1000000 in
theorem shrink_output_bounds (s D rem : ℕ) (A : State (2^s) (shrinkCharge s+rem)) {W : ℕ}
    (hD : 0<D) (old : ShrinkOldCaps s rem W)
    (extra : ShrinkOutputCaps s D (Fintype.card (shrinkRecordState s rem A).Base) W)
    (supply : (shrinkRecordPacking s rem A).Motif → Fin 8 → ℕ)
    (top : ℕ) (size : ∀ m j,supply m j≤top) (widthFit : top<2^W)
    (lay : Bool) (hc : 2≤2*(2^s)+1)
    (good : TagConditions (shrinkRecordPacking s rem A).slots (shift (shrinkRecordPacking s rem A))
      (shrinkRecordPacking s rem A).offset) (ht : 0<tagBits (2^s)) :
    let S := shrinkStage s D
    let P := shrinkRecordPacking s rem A
    let B := shrinkRecordState s rem A
    let stagePad := PhysicalShrink.padding (2*(2^s)+1) (2^s) D
    let bound := shrinkPieceBound s D
    let E := shrinkOutputCodec s rem A old
    Resident.Fits (pad:=stagePad) S P B.order bound E supply ∧
      (∀ p rev j, SlotImage.fields (Resident.successor (pad:=stagePad) S P B.order bound lay hc good ht)
        (Template.tagNumber B.order) (tagOrdinal rem) p rev j<2^W) ∧
      ∀ a, Resident.newWidth (pad:=stagePad) S P B.order bound lay hc good supply a<2^W := by
  intro S P B stagePad bound E
  let N := Fintype.card B.Base
  let t := tagBits (2^s)
  have degree:=shrink_output_degree s D hD
  have baseCount : N≤2^W := (Nat.le_mul_of_pos_right N (Nat.two_pow_pos t)).trans extra.bases
  have encoded (v : B.Base) : (E.base v).val=(B.order v).val :=
    Fin.val_cast_of_lt ((B.order v).isLt.trans_le baseCount)
  have chart (z : BitWord s) : slotCode (w:=W) P z=tagWord (exponent_le old.slots) z :=
    Demand.tag_cast (exponent_le old.slots) z
  have degFits : Graph.liveDegree S+stagePad<2^W := degree.le.trans_lt extra.degree
  have fits : Resident.Fits (pad:=stagePad) S P B.order bound E supply := by
    refine ⟨fun _=>rfl,?_,?_,?_,?_,fun a j=>(size a j).trans_lt widthFit,?_,degree.symm,rfl,
      degFits,⟨extra.pieces,by have:=old.eight;omega,old.slots,old.colors,old.tags⟩,old.residual,by have:=old.eight;omega⟩
    · intro v u same
      exact B.order.injective (Fin.ext ((encoded v).symm.trans ((congrArg Fin.val same).trans (encoded u))))
    · intro u v
      exact (chart (u+v)).trans ((tagWord_add (exponent_le old.slots) u v).trans
        (congrArg₂ BinaryOp.bitXor.eval (chart u).symm (chart v).symm))
    · intro u v
      exact (chart (u-v)).trans ((tagWord_sub (exponent_le old.slots) u v).trans
        (congrArg₂ BinaryOp.bitXor.eval (chart u).symm (chart v).symm))
    · intro e
      exact (Resident.edgeId_le S P B.order bound e).trans_lt extra.keys
    · intro v
      rw [encoded,←Template.tagNumber_val B.order v]
      exact (Template.tagNumber B.order v).isLt.trans_le extra.bases
  refine ⟨fits, ?_, ?_⟩
  · exact Resident.boundFields (Resident.successor (pad:=stagePad) S P B.order bound lay hc good ht)
      (Template.tagNumber B.order) (tagOrdinal rem) extra.bases degFits.le old.residual.le
  · intro a
    exact (Resident.boundWidth (pad:=stagePad) S P B.order bound lay hc good supply size a).trans_lt widthFit


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
