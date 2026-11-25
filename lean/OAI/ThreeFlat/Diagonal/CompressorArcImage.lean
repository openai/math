import OAI.ThreeFlat.Diagonal.CompressorStoredColumns

namespace OAI
/-! # The raw slot image and chronological auxiliary arrays imply every arc read -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.StoredColumns
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Placement
open scoped Fin.CommRing
variable {B H : Type*} {w N c d t l : ℕ} [AddCommGroup H]

structure Extra where
  color : ℕ
  offset : ℕ
  split : ℕ

def addresses (C : SlotImage.Columns) (x : Extra) : ArcColumns (Word w) :=
  let g (i : ℕ) : Word w := (C.graph+C.rows*i:ℕ)
  let z (i : ℕ) : Word w := (x.split+C.rows*i:ℕ)
  ⟨⟨x.color,x.offset,g 0,z 2,z 3,g 3,g 4,z 6,z 7⟩,z 0,z 1,z 4,z 5⟩

structure Auxiliary (P : PackingData B H (BitWord t) (BitWord l) d c) (base : B ≃ Fin N)
    (C : SlotImage.Columns) (x : Extra) (m : Memory w) : Prop where
  color : ∀ b,(m (x.color+(base b).val)).val=(P.color b).val
  offset : ∀ b,(m (x.offset+(base b).val)).val=(tagOrdinal t (P.offset b)).val
  split : ∀ (p : B × Fin d) (back : Bool) (f : Fin 4),
    (m (x.split+C.rows*((if back then 4 else 0)+f.val)+SlotImage.ordinal base p)).val =
      digit c d t f.val (m (SlotImage.cell C base p back 2)).val
  colorFits : x.color+N≤2^w
  offsetFits : x.offset+N≤2^w
  splitFits : x.split+8*C.rows≤2^w
  graphFits : C.graph+6*C.rows≤2^w

theorem row_word (m : Memory w) (a b : ℕ) (h : a+b<2^w) :
    row (words m) (a:Word w) (b:Word w) = m (a+b) := by
  change m ((a:Word w)+(b:Word w)).val = _
  apply congrArg m
  change (a%2^w+b%2^w)%2^w = a+b
  rw [←Nat.add_mod a b (2^w), Nat.mod_eq_of_lt h]

section RawGraph
variable {B H : Type} [AddCommGroup H]

theorem reads (P : PackingData B H (BitWord t) (BitWord l) d c)
    (E : Codec B w c t l) (base : B ≃ Fin N) (C : SlotImage.Columns) (x : Extra)
    (m : Memory w) (width : SlotImage.Edge B (BitWord c × H × BitWord t × BitWord l) d → ℕ)
    (stored : SlotImage.Stored (StageAddress.packedGraph P) base (Demand.laneOrdinal P) C
      (fun i => (m i).val) width)
    (aux : Auxiliary P base C x m) (code : ∀ b,E.base b=((base b).val:Word w))
    (hAdd : ∀ u v,slotCode (w:=w) P (u+v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
    (hSub : ∀ u v,slotCode (w:=w) P (u-v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v)) :
    ArcReads P E (addresses C x) m := by
  let g := StageAddress.packedGraph P
  have bound (v : B × Fin d) : SlotImage.ordinal base v<C.rows :=
    stored.rowCount ▸ SlotImage.ordinal_lt base v
  have raw (v : B × Fin d) (back : Bool) (f : Fin 3) :
      slot (words m) d ((C.graph+C.rows*SlotImage.column back f:ℕ):Word w)
        (E.base v.1) (v.2.val:Word w) =
        ((SlotImage.fields g base (Demand.laneOrdinal P) v back f):Word w) := by
    have cf : SlotImage.column back f<6 := by
      cases back <;> have := f.isLt <;> simp [SlotImage.column] <;> omega
    have huge := Nat.mul_le_mul_left C.rows cf
    have off := bound v
    have span := aux.graphFits
    rw [code,word_slot]
    · exact (Fin.cast_val_eq_self _).symm.trans (congrArg Nat.cast (stored.graph v back f))
    · change C.graph+C.rows*SlotImage.column back f+SlotImage.ordinal base v<2^w
      rw [Nat.mul_succ] at huge
      omega
  have sliced (v : B × Fin d) (back : Bool) (f : Fin 4) :
      slot (words m) d ((x.split+C.rows*((if back then 4 else 0)+f.val):ℕ):Word w)
        (E.base v.1) (v.2.val:Word w) = (shiftField P v back f:Word w) := by
    have cf : (if back then 4 else 0)+f.val<8 := by
      cases back <;> have := f.isLt <;> simp <;> omega
    have huge := Nat.mul_le_mul_left C.rows cf
    have off := bound v
    have span := aux.splitFits
    rw [code,word_slot]
    · exact (Fin.cast_val_eq_self _).symm.trans (congrArg Nat.cast
        ((aux.split v back f).trans (stored_slice P base C _ width stored v back f)))
    · change x.split+C.rows*((if back then 4 else 0)+f.val)+SlotImage.ordinal base v<2^w
      rw [Nat.mul_succ] at huge
      omega
  have col (v : B) : row (words m) (x.color:Word w) (E.base v)=((P.color v).val:Word w) := by
    rw [code,row_word _ _ _ ((Nat.add_lt_add_left (base v).isLt _).trans_le aux.colorFits)]
    exact (Fin.cast_val_eq_self _).symm.trans (congrArg Nat.cast (aux.color v))
  have tag (v : B) : row (words m) (x.offset:Word w) (E.base v)=tagWord E.tags (P.offset v) := by
    rw [code,row_word _ _ _ ((Nat.add_lt_add_left (base v).isLt _).trans_le aux.offsetFits)]
    apply Fin.ext
    exact aux.offset v
  refine ⟨⟨col,tag,?_,?_,?_,?_,?_,?_,?_⟩,hAdd,hSub,?_,?_,?_,?_⟩ <;> intro v i
  · rw [code (P.slots.target (v,i)).1]; exact raw (v,i) false 0
  · rw [code (P.slots.target.symm (v,i)).1]; exact raw (v,i) true 0
  · exact raw (v,i) true 1
  · exact (sliced (v,i) false 2).trans (Demand.tag_cast E.tags (P.siteShift (v,i)).1)
  · exact (sliced (v,i) false 3).trans (Demand.tag_cast E.lanes (P.siteShift (v,i)).2)
  · exact (sliced (v,i) true 2).trans (Demand.tag_cast E.tags (P.siteShift (P.slots.target.symm (v,i))).1)
  · exact (sliced (v,i) true 3).trans (Demand.tag_cast E.lanes (P.siteShift (P.slots.target.symm (v,i))).2)
  · exact (sliced (v,i) false 0).trans (Demand.tag_cast E.colors (P.bitShift (v,i)))
  · exact sliced (v,i) false 1
  · exact (sliced (v,i) true 0).trans (Demand.tag_cast E.colors (P.bitShift (P.slots.target.symm (v,i))))
  · exact sliced (v,i) true 1


end RawGraph
end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.StoredColumns

end OAI
