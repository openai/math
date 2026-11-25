import OAI.ThreeFlat.Diagonal.CompressorPlacementBridge
import OAI.ThreeFlat.Diagonal.CompressorNativeArc
import OAI.ThreeFlat.Diagonal.CompressorLocalIncidence

namespace OAI
/-! # Physical incidence traversal and the three surviving roles -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Placement
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.Compression
open scoped Fin.NatCast
variable {V H : Type*} [AddCommGroup H] {d c w t l : ℕ}
variable (P : PackingData V H (BitWord t) (BitWord l) d c) (E : Codec V w c t l)
variable (G : ArcColumns (Word w)) (m : Memory w)

abbrev slotCode (h : H) : Word w := ((P.slotLabel h).val : Word w)

structure ArcReads extends GraphReads P E G.toColumns m where
  label_add : ∀ u v, slotCode (w:=w) P (u+v) =
    BinaryOp.bitXor.eval (slotCode P u) (slotCode P v)
  label_sub : ∀ u v, slotCode (w:=w) P (u-v) =
    BinaryOp.bitXor.eval (slotCode P u) (slotCode P v)
  forwardBits : ∀ v (i : Fin d), slot (words m) d G.forwardBits (E.base v) (i.val : Word w) =
    tagWord E.colors (P.bitShift (v,i))
  forwardLabel : ∀ v (i : Fin d), slot (words m) d G.forwardLabel (E.base v) (i.val : Word w) =
    slotCode P (P.slotShift (v,i))
  backBits : ∀ v (i : Fin d), slot (words m) d G.backBits (E.base v) (i.val : Word w) =
    tagWord E.colors (P.bitShift (P.slots.target.symm (v,i)))
  backLabel : ∀ v (i : Fin d), slot (words m) d G.backLabel (E.base v) (i.val : Word w) =
    slotCode P (P.slotShift (P.slots.target.symm (v,i)))

def encodeEnds (a : Arc V H (BitWord t) (BitWord l) d c) : Ends (Word w) :=
  ⟨posCode P E (sourcePosition a),posCode P E (sourcePosition (P.actual a)),(a.1.2.val : Word w)⟩

variable {P E G m} (R : ArcReads P E G m)
include R

theorem out_code (x : Computability.VPVNP.Compression.Position V H (BitWord t) (BitWord l) c) (i : Fin d) :
    ends (words m) G d false (posCode P E x) (i.val : Word w) =
      encodeEnds P E ((x.1,i),x.2) := by
  rcases x with ⟨s,u,h⟩
  simp only [ends,Bool.false_eq_true,ite_false,encodeEnds,PackingData.actual_apply,sourcePosition,posCode]
  congr 2
  · exact forward_site R.toGraphReads s i
  · change BinaryOp.bitXor.eval (tagWord E.colors u)
      (slot (words m) d G.forwardBits (E.base s.1) (i.val : Word w)) = _
    rw [R.forwardBits,tagWord_add]
  · change BinaryOp.bitXor.eval (slotCode P h)
      (slot (words m) d G.forwardLabel (E.base s.1) (i.val : Word w)) = slotCode P (h+_)
    rw [R.forwardLabel,R.label_add]

theorem in_code (x : Computability.VPVNP.Compression.Position V H (BitWord t) (BitWord l) c) (i : Fin d) :
    ends (words m) G d true (posCode P E x) (i.val : Word w) =
      encodeEnds P E (P.actual.symm ((x.1,i),x.2)) := by
  unfold encodeEnds
  rw [P.actual.apply_symm_apply]
  rcases x with ⟨s,u,h⟩
  simp only [ends,ite_true,PackingData.actual_symm_apply,sourcePosition,posCode]
  congr 2
  · exact backward_site R.toGraphReads s i
  · change BinaryOp.bitXor.eval (tagWord E.colors u)
      (slot (words m) d G.backBits (E.base s.1) (i.val : Word w)) = _
    rw [R.backBits,tagWord_sub]
  · change BinaryOp.bitXor.eval (slotCode P h)
      (slot (words m) d G.backLabel (E.base s.1) (i.val : Word w)) = slotCode P (h-_)
    rw [R.backLabel,R.label_sub]
  · exact R.backSlot s.1 i

theorem local_arc (layout thin incoming : Bool) (s : Computability.VPVNP.Compression.Site V (BitWord t) (BitWord l))
    (i j : Fin d) (u : BitWord c) :
    fromChild (words m) G d layout thin incoming (siteCode E s) (i.val : Word w) (tagWord E.colors u)
      (j.val : Word w) =
      encodeEnds P E (Local.incidentArc P layout s ((thin,i,u),incoming,j)) := by
  unfold fromChild
  rw [child_code R.toGraphReads]
  cases incoming with
  | false => exact out_code R _ j
  | true => exact in_code R _ j

theorem roles_code (layout : Bool) (a : P.Motif) :
    roleSites (words m) G d layout (encodeEnds P E a.val) =
      ⟨siteCode E (P.roleA a),siteCode E (P.roleB a),siteCode E (P.roleD layout a),1⟩ := by
  let x := sourcePosition a.val
  let y := sourcePosition (P.actual a.val)
  have select_eq (flag : Word w) (u v : Computability.VPVNP.Compression.Position V H (BitWord t) (BitWord l) c) :
      Position.select (words m) flag (posCode P E u) (posCode P E v) =
        posCode P E (if flag = 1 then u else v) := by
    by_cases h : flag=1 <;> simp [Position.select,Site.select,words,h,posCode,siteCode]
  let flag := thickBit (words m) G.toColumns (posCode P E x)
  let otherFlag := thickBit (words m) G.toColumns (posCode P E y)
  have hx : flag=1 ↔ P.thick x := thick_bit R.toGraphReads x
  have hy : otherFlag=1 ↔ P.thick y := thick_bit R.toGraphReads y
  have selected (a b : Computability.VPVNP.Compression.Position V H (BitWord t) (BitWord l) c) :
      Position.select (words m) flag (posCode P E a) (posCode P E b) =
        posCode P E (if P.thick x then a else b) := by
    rw [select_eq]
    by_cases h : P.thick x
    · rw [ite_eq_left (hx.mpr h),ite_eq_left h]
    · rw [ite_eq_right (hx.not.mpr h),ite_eq_right h]
  have hc : Position.select (words m) flag (posCode P E y) (posCode P E x) = posCode P E (P.C a) :=
    selected y x
  have hd : Position.select (words m) flag (posCode P E x) (posCode P E y) = posCode P E (P.D a) :=
    selected x y
  have good : (words m).choose flag ((words m).lit 1)
      ((words m).choose otherFlag ((words m).lit 1) ((words m).lit 0) ((words m).lit 1)) ((words m).lit 1) =
      (1 : Word w) := by
    change (if flag=1 then (if otherFlag=1 then 0 else 1) else 1) = 1
    by_cases h : P.thick x
    · have no : ¬P.thick y := fun q => a.property ⟨h,q⟩
      rw [ite_eq_left (hx.mpr h),ite_eq_right (hy.not.mpr no)]
    · rw [ite_eq_right (hx.not.mpr h)]
  unfold roleSites
  change RoleSites.mk
    (toggle (words m) G.toColumns (Position.select (words m) flag (posCode P E y) (posCode P E x)).site)
    (forward (words m) G.toColumns d
      (toggle (words m) G.toColumns (Position.select (words m) flag (posCode P E y) (posCode P E x)).site)
      (Position.select (words m) flag (posCode P E y) (posCode P E x)).slot)
    (owner (words m) G.toColumns d layout (Position.select (words m) flag (posCode P E x) (posCode P E y)))
    ((words m).choose flag ((words m).lit 1)
      ((words m).choose otherFlag ((words m).lit 1) ((words m).lit 0) ((words m).lit 1))
      ((words m).lit 1)) = _
  rw [hc,hd,good]
  change RoleSites.mk (toggle (words m) G.toColumns (siteCode E (P.C a).1))
    (forward (words m) G.toColumns d (toggle (words m) G.toColumns (siteCode E (P.C a).1))
      ((P.slotLabel (P.C a).2.2).val : Word w)) (owner (words m) G.toColumns d layout (posCode P E (P.D a))) 1 = _
  rw [toggle_site R.toGraphReads,forward_site R.toGraphReads,owner_code R.toGraphReads]; rfl

end ThreeFlat.Diagonal.CompressorPacking.Native.Placement

end OAI
