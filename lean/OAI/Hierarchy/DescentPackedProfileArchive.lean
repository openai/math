import OAI.Hierarchy.DescentPackedProfileWide
import OAI.Hierarchy.DescentTerminalEpochChart
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Simultaneous immutable packed matching windows at their real per-stage addresses -/
namespace Hierarchy.DescentPackedProfileArchive
open DescentTerminalEpochChart DescentTerminalEpochBits DescentPackedProfileWide DescentPackedProfileWindow
open ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w t : ℕ} {A : Type}

/-- This is the native profile-pass readback at every physical index of its
dyadic raw bank, including unused cells and the two-word window guard. -/
def Stored (a : Source A) (d R : ℕ) (extend : width a.C ≤ d) (raw : Bank) (z : A→Bool) (m : Memory w) : Prop :=
  ∀j < raw.size,m (raw.base+j)=((word d R (wideCell a.pin z d extend) j).val:Word w)

structure Entry (A : Type) where
  source : Source A
  digit : ℕ
  grain : ℕ
  extend : width source.C ≤ digit
  raw : Bank

def inside (b : Bank) (a : ℕ) : Prop:=b.base ≤ a ∧ a < b.base+b.size

def Separated (rows : Fin t→Entry A) : Prop :=
  ∀i j : Fin t,i ≠ j→(rows i).raw.base+(rows i).raw.size ≤ (rows j).raw.base ∨
    (rows j).raw.base+(rows j).raw.size ≤ (rows i).raw.base

theorem separated_of_order (rows : Fin t→Entry A)
    (next : ∀i j : Fin t,i < j→(rows i).raw.base+(rows i).raw.size ≤ (rows j).raw.base) : Separated rows := by
  intro i j ne
  rcases lt_or_gt_of_ne ne with h|h
  · exact Or.inl (next i j h)
  · exact Or.inr (next j i h)

theorem unique (rows : Fin t→Entry A) (apart : Separated rows) (a : ℕ) {i j : Fin t}
    (left : inside (rows i).raw a) (right : inside (rows j).raw a) : i=j := by
  by_contra ne
  obtain order|order:=apart i j ne <;> rcases left with ⟨l,r⟩ <;> rcases right with ⟨l',r'⟩ <;> omega

/-- The chosen bank depends only on the address and fixed physical packet
layout. All blocks are installed together over the earlier original tapes. -/
def image (rows : Fin t→Entry A) (z : A→Bool) (old : Memory w) (a : ℕ) : Word w :=
  if h : ∃i,inside (rows i).raw a then
    let e:=rows h.choose
    ((word e.digit e.grain (wideCell e.source.pin z e.digit e.extend) (a-e.raw.base)).val:Word w)
  else old a

theorem at_bank (rows : Fin t→Entry A) (apart : Separated rows) (z : A→Bool) (old : Memory w)
    (i : Fin t) (j : ℕ) (fit : j < (rows i).raw.size) :
    image rows z old ((rows i).raw.base+j)=
      ((word (rows i).digit (rows i).grain (wideCell (rows i).source.pin z (rows i).digit (rows i).extend) j).val:Word w) := by
  let addr:=(rows i).raw.base+j
  have member : inside (rows i).raw addr:=by unfold inside addr;omega
  have has : ∃k,inside (rows k).raw addr:=⟨i,member⟩
  have eqn:=unique rows apart addr has.choose_spec member
  change image rows z old addr=_
  unfold image
  rw [dite_eq_left has]
  change ((word (rows has.choose).digit (rows has.choose).grain
    (wideCell (rows has.choose).source.pin z (rows has.choose).digit (rows has.choose).extend)
    (addr-(rows has.choose).raw.base)).val:Word w)=_
  rw [eqn]
  simp [addr]

theorem stored (rows : Fin t→Entry A) (apart : Separated rows) (z : A→Bool) (old : Memory w) (i : Fin t) :
    Stored (rows i).source (rows i).digit (rows i).grain (rows i).extend (rows i).raw z (image rows z old) :=
  at_bank rows apart z old i

theorem frame (rows : Fin t→Entry A) (z : A→Bool) (old : Memory w) {a : ℕ}
    (away : ∀i,¬inside (rows i).raw a) : image rows z old a=old a := by
  have h : ¬∃i,inside (rows i).raw a:=fun ⟨i,hi⟩=>away i hi
  simp only [image,dite_eq_right h]

theorem before (rows : Fin t→Entry A) (z : A→Bool) (old : Memory w) {a : ℕ}
    (early : ∀i,a < (rows i).raw.base) : image rows z old a=old a :=
  frame rows z old (fun i h=>(Nat.not_le_of_gt (early i)) h.1)

theorem preserve (a : Source A) (d R : ℕ) (extend : width a.C ≤ d) (raw : Bank) (z : A→Bool)
    (m after : Memory w) (st : Stored a d R extend raw z m)
    (keep : ∀j < raw.size,after (raw.base+j)=m (raw.base+j)) : Stored a d R extend raw z after :=
  fun j hj=>(keep j hj).trans (st j hj)

/-- The full matching archive on a fixed schedule is a projection of the
same original Boolean candidate that is checked by the packed epoch verifier. -/
def pin (rows : Fin t→Entry A) (previous : ℕ→ℕ→A⊕Bool) (a j : ℕ) : A⊕Bool :=
  if h : ∃i,inside (rows i).raw a then
    let e:=rows h.choose
    widePin e.source.pin e.digit e.grain (a-e.raw.base) j
  else previous a j

theorem pin_word (rows : Fin t→Entry A) (z : A→Bool) (old : Memory w)
    (small : ∀i,(rows i).digit*(rows i).grain ≤ w)
    (previous : ℕ→ℕ→A⊕Bool) (prior : ∀a j,(previous a j).elim z id=(old a).val.testBit j)
    (a j : ℕ) : (pin rows previous a j).elim z id=(image rows z old a).val.testBit j := by
  by_cases has : ∃i,inside (rows i).raw a
  · let e:=rows has.choose
    let packed:=word e.digit e.grain (wideCell e.source.pin z e.digit e.extend) (a-e.raw.base)
    have room : packed.val < 2^w:=packed.isLt.trans_le (Nat.pow_le_pow_right (by decide) (small has.choose))
    simp only [pin,image,dite_eq_left has]
    change (widePin e.source.pin e.digit e.grain (a-e.raw.base) j).elim z id=(packed.val:Word w).val.testBit j
    rw [Fin.val_cast_of_lt room]
    exact wide_bit e.source.pin z e.digit e.extend e.grain (a-e.raw.base) j
  · simpa only [pin,image,dite_eq_right has] using prior a j

end
end Hierarchy.DescentPackedProfileArchive

end OAI
