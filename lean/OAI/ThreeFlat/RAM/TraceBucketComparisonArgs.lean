import OAI.ThreeFlat.RAM.TraceBucketArithmetic

namespace OAI
/-! # The candidate row read for an outgoing physical reservation -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open Diagonal.TraceSourceOwner
open scoped Fin.CommRing
variable {W : ℕ}

structure Candidate where
  tag : ℕ
  offset : ℕ
  lo : ℕ
  slot : ℕ
  leg : ℕ
  own : ℕ
  mask : ℕ
  dest : ℕ
  source : ℕ
  home : ℕ
  localSlot : ℕ

def candidate (s : Layout) (m : ℕ→ℕ) (lane row : ℕ) : Candidate :=
  let t := row-(s.relays+s.gates)
  let o := t/s.per
  let lo := (t/(s.slots*3))%s.lowRows
  let slot := (t/3)%s.slots
  let leg := t%3
  let own := lane*s.lowRows+lo
  let mask := m (s.masks+o)
  let dest := own ^^^ mask
  let x := m (s.readAt dest slot leg)
  ⟨t,o,lo,slot,leg,own,mask,dest,x,ownerAt s.shape 1 dest x,
    ((locate s.shape (x-(2+s.shape.header))).1%s.lowRows)*s.shape.stride+(locate s.shape (x-(2+s.shape.header))).2⟩

def cmpInputs (s : Layout) (m : ℕ→ℕ) (lane row field : ℕ) : Fin 15→ℕ :=
  let a := candidate s m lane row
  ![field,a.source,a.home,a.own,a.offset,s.depth,s.shape.header,s.pinLow lane,s.pinCount lane,
    s.bank+s.bank,a.localSlot,a.mask/s.lowRows%2,s.tags,a.tag,s.equalId]

/-- All large address bounds concern only this physical receiver, this
source, or a complete table region. The two owner calculations share
one width margin. -/
structure CompareFits (W b : ℕ) (s : Layout) (v : Fin 4→Word W) (m : Memory W) : Prop where
  afterGates : s.relays+s.gates≤(v 0).val
  literals : 3<2^W ∧ s.slots*3<2^W ∧ s.per<2^W
  header : 2+s.shape.header<2^W
  interval : s.pinLow (v 2).val+2*s.lowRows<2^W
  maskRead : s.masks+((v 0).val-(s.relays+s.gates))/s.per<2^W
  receiver : (candidate s (fun n => (m n).val) (v 2).val (v 0).val).own<2^W
  record : let a := candidate s (fun n => (m n).val) (v 2).val (v 0).val
           s.readAt a.dest a.slot a.leg<2^W
  ownerArgs : let a := candidate s (fun n => (m n).val) (v 2).val (v 0).val
              ∀ i,TraceOwnerFormula.vars s.shape 1 a.source a.dest i<2^b
  slotArgs : let a := candidate s (fun n => (m n).val) (v 2).val (v 0).val
             ∀ i,TraceOwnerFormula.vars s.shape 1 (a.source-(2+s.shape.header)) 0 i<2^b
  privateRow : let a := candidate s (fun n => (m n).val) (v 2).val (v 0).val
               (locate s.shape (a.source-(2+s.shape.header))).1<2^W
  margin : 5*b+128≤W
  numeric : ∀ i,cmpInputs s (fun n => (m n).val) (v 2).val (v 0).val (v 1).val i<2^W

theorem cmpArgs_value (s : Layout) (v : Fin 4→Word W) (data : Fin 1→Word W) (m : Memory W)
    (b : ℕ) (h : CompareFits W b s v m) :
    operands (cmpArgs s) data m v=cmpInputs s (fun n => (m n).val) (v 2).val (v 0).val (v 1).val := by
  let a := candidate s (fun n => (m n).val) (v 2).val (v 0).val
  let E := Term W 1 4
  let lit (n : ℕ) : E := .literal n
  let t : E := .binary .sub (.result 0) (lit (s.relays+s.gates))
  let o : E := .binary .div t (lit s.per)
  let lo : E := .binary .mod (.binary .div t (lit (s.slots*3))) (lit s.lowRows)
  let slot : E := .binary .mod (.binary .div t (lit 3)) (lit s.slots)
  let leg : E := .binary .mod t (lit 3)
  let own : E := .binary .add (laneBase s) lo
  let mask : E := .load (.binary .add (lit s.masks) o)
  let dest : E := .binary .bitXor own mask
  let x : E := raw s dest slot leg
  let offset := lit (2+s.shape.header)
  let z : E := .select .lt x offset (lit 0) (.binary .sub x offset)
  have ini : (Term.result 0 : E).eval data m v=((v 0).val : Word W) := by simp [Term.eval]
  have leaf (z : ℕ) : (lit z).eval data m v=(z : Word W) := Term.eval_literal ..
  have bin := @binary_value W 4 data m v
  have tw : a.tag<2^W := (Nat.sub_le _ _).trans_lt (v 0).isLt
  have lw : s.lowRows<2^W := by have := h.interval; omega
  have cw : s.slots<2^W := by have := h.literals; omega
  have three := h.literals.1
  have ht : t.eval data m v=(a.tag : Word W) := bin .sub ini (leaf _) h.afterGates
  have ho : o.eval data m v=(a.offset : Word W) := bin .div ht (leaf _) ⟨tw,h.literals.2.2⟩
  have hlo : lo.eval data m v=(a.lo : Word W) :=
    bin .mod (bin .div ht (leaf _) ⟨tw,h.literals.2.1⟩) (leaf _) ⟨(Nat.div_le_self ..).trans_lt tw,lw⟩
  have hslot : slot.eval data m v=(a.slot : Word W) :=
    bin .mod (bin .div ht (leaf _) ⟨tw,three⟩) (leaf _) ⟨(Nat.div_le_self ..).trans_lt tw,cw⟩
  have hleg : leg.eval data m v=(a.leg : Word W) := bin .mod ht (leaf _) ⟨tw,three⟩
  have hown : own.eval data m v=(a.own : Word W) := bin .add (laneBase_value s v data m) hlo trivial
  have hma : mask.eval data m v=(a.mask : Word W) := by
    change (Term.load _).eval data m v=_
    rw [Term.eval_load,bin .add (leaf _) ho trivial]
    change m (((s.masks+a.offset : ℕ) : Word W).val) = ((m (s.masks+a.offset)).val : Word W)
    rw [Fin.val_cast_of_lt (show s.masks+a.offset<2^W from h.maskRead),Fin.cast_val_eq_self]
  have maskSmall : a.mask<2^W := (m _).isLt
  have hdest : dest.eval data m v=(a.dest : Word W) := bin .bitXor hown hma ⟨h.receiver,maskSmall⟩
  have hx : x.eval data m v=(a.source : Word W) := by
    simpa [x,a,candidate] using raw_value s v data m dest slot leg a.dest a.slot a.leg hdest hslot hleg h.record
  have sourceSmall : a.source<2^W := (m _).isLt
  have hz : z.eval data m v=(a.source-(2+s.shape.header) : ℕ) := cut_value data m v hx (leaf _) sourceSmall h.header
  have home := direct_owner s data m v x dest a.source a.dest b hx hdest h.ownerArgs h.margin
  have off := TraceOwnerFormula.direct_eval .slot s.shape 1 _ 0 z (lit 0) data m v hz (leaf _) h.slotArgs h.margin
  rw [TraceOwnerFormula.slot_natural] at off
  have hr := TraceOwnerFormula.direct_eval .row s.shape 1 _ 0 z (lit 0) data m v hz (leaf _) h.slotArgs h.margin
  rw [TraceOwnerFormula.row_natural] at hr
  have pos := bin .mod hr (leaf s.lowRows) ⟨h.privateRow,lw⟩
  have endPos := bin .add (bin .mul pos (leaf s.shape.stride) trivial) off trivial
  have pin := pinStart_value s v data m
  have count := ext_value s v data m (by have := h.header; omega) h.interval
  have side := bin .mod (bin .div hma (leaf s.lowRows) ⟨maskSmall,lw⟩) (leaf 2)
    ⟨(Nat.div_le_self ..).trans_lt maskSmall,by omega⟩
  funext i
  have word : ((cmpArgs s i : E)).eval data m v=(cmpInputs s (fun j => (m j).val) (v 2).val (v 0).val (v 1).val i : Word W) := by
    fin_cases i
    · exact (show (↑(v 1).val : Word W) = v 1 by simp).symm
    · exact hx
    · exact home
    · exact hown
    · exact ho
    · rfl
    · rfl
    · exact pin
    · exact count
    · rfl
    · exact endPos
    · exact side
    · rfl
    · exact ht
    · rfl
  exact (congrArg Fin.val word).trans (Fin.val_cast_of_lt (h.numeric i))

end ThreeFlat.RAM.TraceBucketAtom

end OAI
