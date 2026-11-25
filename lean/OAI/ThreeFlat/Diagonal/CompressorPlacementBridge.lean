import OAI.ThreeFlat.Diagonal.CompressorOwnerRows
import OAI.ThreeFlat.Diagonal.CompressorNativePlacement
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding

namespace OAI
/-! # The native site and child records encode the actual compressor placement -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Placement
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.Compression
open scoped Fin.NatCast
variable {V H : Type*} [AddCommGroup H] {w d c t l : ℕ}
variable (P : PackingData V H (BitWord t) (BitWord l) d c)

structure Codec (V : Type*) (w c t l : ℕ) where
  base : V → Word w
  colors : c ≤ w
  tags : t ≤ w
  lanes : l ≤ w

variable (E : Codec V w c t l) (C : Columns (Word w)) (m : Memory w)

def siteCode (s : Computability.VPVNP.Compression.Site V (BitWord t) (BitWord l)) : Site (Word w) :=
  ⟨E.base s.1,tagWord E.tags s.2.1,tagWord E.lanes s.2.2⟩

def posCode (x : Computability.VPVNP.Compression.Position V H (BitWord t) (BitWord l) c) : Position (Word w) :=
  ⟨siteCode E x.1,tagWord E.colors x.2.1,((P.slotLabel x.2.2).val : Word w)⟩

/-- All table hypotheses are individual memory reads of one of the nine public columns. -/
structure GraphReads : Prop where
  color : ∀ v, row (words m) C.color (E.base v) = ((P.color v).val : Word w)
  offset : ∀ v, row (words m) C.offset (E.base v) = tagWord E.tags (P.offset v)
  dst : ∀ v (i : Fin d), slot (words m) d C.dst (E.base v) (i.val : Word w) =
    E.base (P.slots.target (v,i)).1
  src : ∀ v (i : Fin d), slot (words m) d C.src (E.base v) (i.val : Word w) =
    E.base (P.slots.target.symm (v,i)).1
  backSlot : ∀ v (i : Fin d), slot (words m) d C.backSlot (E.base v) (i.val : Word w) =
    ((P.slots.target.symm (v,i)).2.val : Word w)
  fTag : ∀ v (i : Fin d), slot (words m) d C.forwardTag (E.base v) (i.val : Word w) =
    tagWord E.tags (P.siteShift (v,i)).1
  fLane : ∀ v (i : Fin d), slot (words m) d C.forwardLane (E.base v) (i.val : Word w) =
    tagWord E.lanes (P.siteShift (v,i)).2
  bTag : ∀ v (i : Fin d), slot (words m) d C.backTag (E.base v) (i.val : Word w) =
    tagWord E.tags (P.siteShift (P.slots.target.symm (v,i))).1
  bLane : ∀ v (i : Fin d), slot (words m) d C.backLane (E.base v) (i.val : Word w) =
    tagWord E.lanes (P.siteShift (P.slots.target.symm (v,i))).2

variable {P E C m} (R : GraphReads P E C m)
include R

omit [AddCommGroup H] in
theorem toggle_site (s : Computability.VPVNP.Compression.Site V (BitWord t) (BitWord l)) :
    toggle (words m) C (siteCode E s) = siteCode E (P.offsetSite s) := by
  rcases s with ⟨v,z,y⟩
  change Placement.Site.mk (E.base v) (BinaryOp.bitXor.eval _ (row (words m) C.offset (E.base v))) _ =
    Placement.Site.mk _ (tagWord E.tags (z+P.offset v)) _
  rw [R.offset,tagWord_add]
  rfl

omit [AddCommGroup H] in
theorem toggle_inverse (s : Computability.VPVNP.Compression.Site V (BitWord t) (BitWord l)) :
    toggle (words m) C (siteCode E s) = siteCode E (P.offsetSite.symm s) := by
  rcases s with ⟨v,z,y⟩
  change Placement.Site.mk (E.base v) (BinaryOp.bitXor.eval _ (row (words m) C.offset (E.base v))) _ =
    Placement.Site.mk _ (tagWord E.tags (z-P.offset v)) _
  rw [R.offset,tagWord_sub]
  rfl

omit [AddCommGroup H] in
theorem forward_site (s : Computability.VPVNP.Compression.Site V (BitWord t) (BitWord l)) (i : Fin d) :
    forward (words m) C d (siteCode E s) (i.val : Word w) =
      siteCode E (P.siteGraph.target (s,i)).1 := by
  rcases s with ⟨v,z,y⟩
  simp only [forward,siteCode,R.dst,R.fTag,R.fLane]
  change Placement.Site.mk _ (BinaryOp.bitXor.eval _ _) (BinaryOp.bitXor.eval _ _) =
    Placement.Site.mk _ (tagWord E.tags _) (tagWord E.lanes _)
  congr 1 <;> exact (tagWord_add _ _ _).symm

omit [AddCommGroup H] in
theorem backward_site (s : Computability.VPVNP.Compression.Site V (BitWord t) (BitWord l)) (i : Fin d) :
    backward (words m) C d (siteCode E s) (i.val : Word w) =
      siteCode E (P.siteGraph.target.symm (s,i)).1 := by
  rcases s with ⟨v,z,y⟩
  simp only [backward,siteCode,R.src,R.bTag,R.bLane]
  change Placement.Site.mk _ (BinaryOp.bitXor.eval _ _) (BinaryOp.bitXor.eval _ _) =
    Placement.Site.mk _ (tagWord E.tags _) (tagWord E.lanes _)
  congr 1 <;> exact (tagWord_sub _ _ _).symm

omit R in
theorem read_bit {cw : ℕ} (fit : cw ≤ w) (u : BitWord cw) (i : Fin cw) :
    BinaryOp.bitAnd.eval (BinaryOp.shiftRight.eval (tagWord fit u) (i.val : Word w)) 1 =
      ((u i).val : Word w) := by
  have iw : i.val < w := i.isLt.trans_le fit
  have iw' : i.val < 2^w := iw.trans Nat.lt_two_pow_self
  have wi : 1 < 2^w := Nat.one_lt_two_pow (by omega)
  have bits : (tagOrdinal cw u).val / 2^i.val % 2 = (u i).val :=
    congrArg Fin.val (congrFun ((tagOrdinal cw).symm_apply_apply u) i)
  have shr : (tagOrdinal cw u).val / 2^i.val < 2^w :=
    (Nat.div_le_self ..).trans_lt (tagWord fit u).isLt
  apply Fin.ext
  simp [BinaryOp.eval,Fin.val_natCast,Nat.mod_eq_of_lt iw',iw,
    Nat.shiftRight_eq_div_pow,tagWord,Nat.mod_eq_of_lt shr,Nat.mod_eq_of_lt wi,bits]

omit [AddCommGroup H] in
theorem thick_bit (x : Computability.VPVNP.Compression.Position V H (BitWord t) (BitWord l) c) :
    thickBit (words m) C (posCode P E x) = 1 ↔ P.thick x := by
  have pos : 1 < 2^w := Nat.one_lt_two_pow (by
    have h := (P.color x.1.1).isLt
    have := E.colors
    omega)
  have cast_bit (b : Fin 2) : ((b.val : Word w) = 1) ↔ b = 1 := by
    constructor
    · intro h
      apply Fin.ext
      have bound : b.val < 2^w := b.isLt.trans_le (show 2 ≤ 2^w from pos)
      simpa [Fin.val_natCast, Fin.val_one, Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt pos] using
        congrArg (fun z : Word w => z.val) h
    · rintro rfl
      rfl
  change BinaryOp.bitAnd.eval (BinaryOp.shiftRight.eval (tagWord E.colors x.2.1)
    (row (words m) C.color (E.base x.1.1))) 1 = 1 ↔ _
  rw [R.color, read_bit]
  exact cast_bit (x.2.1 (P.color x.1.1))

omit [AddCommGroup H] in
theorem owner_code (layout : Bool) (x : Computability.VPVNP.Compression.Position V H (BitWord t) (BitWord l) c) :
    owner (words m) C d layout (posCode P E x) = siteCode E (P.placement layout x) := by
  let f := thickBit (words m) C (posCode P E x)
  have choose (u v : Site (Word w)) :
      (⟨(words m).choose f 1 u.base v.base,(words m).choose f 1 u.tag v.tag,
        (words m).choose f 1 u.lane v.lane⟩ : Site (Word w)) = if f=1 then u else v := by
    by_cases h : f=1 <;> simp [words,h]
  let shifted := toggle (words m) C (siteCode E x.1)
  change _ = _
  rw [show owner (words m) C d layout (posCode P E x) = _ from
    choose (siteCode E x.1) (if layout then forward (words m) C d shifted ((P.slotLabel x.2.2).val:Word w) else shifted)]
  by_cases h : P.thick x
  · have hf : f=1 := (thick_bit R x).2 h
    simp [hf,h,PackingData.placement]
  · have hf : f≠1 := fun a => h ((thick_bit R x).1 a)
    cases layout <;> simp only [hf,ite_false,shifted,h,ite_false,ite_true,Bool.false_eq_true,toggle_site R,
      forward_site R,PackingData.placement,PackingData.assignedBundle]

omit [AddCommGroup H] in
theorem child_code (layout thin : Bool) (s : Computability.VPVNP.Compression.Site V (BitWord t) (BitWord l))
    (i : Fin d) (u : BitWord c) :
    child (words m) C d layout thin (siteCode E s) (i.val : Word w) (tagWord E.colors u) =
      posCode P E (Owner.child P layout s (thin,i,u)) := by
  cases thin
  · cases layout <;> simp [child,Owner.child,posCode]
  · cases layout
    · change Placement.Position.mk (toggle (words m) C (siteCode E s)) _ _ =
        Placement.Position.mk (siteCode E (P.offsetSite.symm s)) _ _
      rw [toggle_inverse R]
      simp [Owner.child,Owner.port]
    · change Placement.Position.mk (toggle (words m) C (backward (words m) C d (siteCode E s) _)) _ _ =
        Placement.Position.mk (siteCode E (P.offsetSite.symm ((P.siteGraph.target.symm (s,i)).1))) _ _
      rw [backward_site R,toggle_inverse R]
      simp only [Owner.child,Owner.port,ite_true,Equiv.apply_symm_apply]
      congr 1
      exact R.backSlot s.1 i


end ThreeFlat.Diagonal.CompressorPacking.Native.Placement

end OAI
