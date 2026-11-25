import OAI.ThreeFlat.Diagonal.CompressorPhysicalField

namespace OAI
/-! # Word value of the four padding projections in the regular physical layout -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement Graph
open scoped Fin.NatCast
variable {B : Type*} {w d n N t l : ℕ}

theorem physical_pad (cell : Word w) (m : Memory w) (vs : Fin 1 → Word w) (S : Stage)
    (b : B ≃ Fin N) (A : LiftedSlots (B × BitWord t) d (BitWord l))
    (ht : 0<t) (oneFit : 1<2^w) (p : (B × BitWord t) × Fin n)
    (fit : (tagNumber b p.1).val<2^w) (lay rev : Bool) (f : Fin 3) (dest : F)
    (bv : Formula.value (fun _=>cell) m vs (.op .div (.op .sub (.reg 0) dest) (.lit S.outputDegree)) =
      ((tagNumber b p.1).val:Word w))
    (iv : Formula.value (fun _=>cell) m vs (.op .mod (.op .sub (.reg 0) dest) (.lit S.outputDegree)) =
      ((d+p.2.val:ℕ):Word w))
    (pad : ¬ ((d+p.2.val:ℕ):Word w)<(S.liveDegree:Word w)) :
    let G := tagPadding (V:=B) (L:=BitWord l) (tagOne ht) (tagOne_ne ht) n
    Formula.value (fun _=>cell) m vs (update S lay rev (graphField f) dest)=
      ((SlotImage.fields (CompressorRefresh.union A G) (tagNumber b) (tagOrdinal l)
        (CompressorRefresh.rightRow p) rev f):Word w) := by
  dsimp only
  rw [CompressorRefresh.fields_right]
  have word (j : Fin 3) := padded_field cell m vs S lay rev (graphField j) dest _ _ bv iv pad
  revert f
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))
  · rw [word 0]
    change BinaryOp.bitXor.eval ((tagNumber b p.1).val:Word w) (1:Word w) = _
    rw [show (1:Word w)=((1:ℕ):Word w) from rfl,op_cast .bitXor (tagNumber b p.1).val 1 ⟨fit,oneFit⟩]
    apply congrArg Nat.cast
    change ((tagNumber b p.1).val ^^^ 1)=(tagNumber b _).val
    rw [tagNumber_val,tagNumber_val]
    have coords := padding_neighbor (L:=BitWord l) (fun z=>(b z).val) ht rev p.1.1 p.1.2 p.2
    cases rev <;> exact coords
  · rcases p with ⟨⟨v,z⟩,j⟩
    cases rev <;> exact word 1
  · have hz : (tagOrdinal l (0:BitWord l)).val=0 := by
      have eq := tagOrdinal_add (0:BitWord l) 0
      simpa only [zero_add,Nat.xor_self] using eq
    simpa [graphField,SlotImage.fields,SlotImage.shift,tagPadding,hz] using word 2


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template

end OAI
