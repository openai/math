import OAI.Hierarchy.DescentRangeRegisterType
import OAI.Hierarchy.DescentRangePage
import OAI.Hierarchy.DescentRegisterTypes
import OAI.Hierarchy.DescentPreviousOperandLayout
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! The live packed argument bank and all three scalar reads, independently of the date that produced the bank. -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSixParty DescentKernelHistory DescentOperandStateBanks
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentDatedAddressBook
open DescentDatedPriorOperand ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

private def physicalChunk {G L : ℕ} (pos : 0<L) (g : Fin G) : Fin (chunks G L) :=
  ⟨g.val/L,by
    change g.val/L<(G+L-1)/L
    apply (Nat.le_div_iff_mul_le pos).2
    rw [Nat.succ_mul]
    have bound:=Nat.div_mul_le_self g.val L
    have inside:=g.isLt
    omega⟩

/-- An aligned carrier needs both a packed group and an actual local node number.
The former is decoded using Euclidean division and the latter by the native SIMD codec. -/
def fromRAM {w : ℕ} {B : BitDescription W} (a : PriorResetArchive) (l : Layout) (fieldBits : ℕ)
    (m : Memory w) (pos : 0<l.lanes)
    (block : NodeOrder.All B→Fin l.blocks) (host : NodeOrder.All B→Fin l.hosts)
    (groupOf : NodeOrder.All B→Fin l.groups) (number : NodeOrder.All B→Fin l.nodes) : Register B where
  field:=fieldBits
  nodes:=l.nodes
  number:=number
  packed x i f:= if live : i<l.operands then
    let bank:=previousBank l a.arguments (block x) (DescentOperandStateBanks.page (page f) ⟨i,live⟩)
    let r:=(row l.hosts l.groups l.lanes (host x,physicalChunk pos (groupOf x))).val
    let full:Cell (((fieldBits)*l.nodes)*l.lanes):=((m (bank.base+r)).val:ℕ)
    (encode ((fieldBits)*l.nodes) l.lanes).symm full ⟨(groupOf x).val%l.lanes,Nat.mod_lt _ pos⟩
    else 0

variable {w : ℕ} {B : BitDescription W} (a : PriorResetArchive) (l : Layout) (fieldBits : ℕ)
    (m : Memory w) (pos : 0<l.lanes)
    (block : NodeOrder.All B→Fin l.blocks) (host : NodeOrder.All B→Fin l.hosts)
    (groupOf : NodeOrder.All B→Fin l.groups) (number : NodeOrder.All B→Fin l.nodes)
local notation "reg" => fromRAM a l fieldBits m pos block host groupOf number

theorem unallocated (x : NodeOrder.All B) (i : ℕ) (f : Fin 3) (past : l.operands≤ i) :
    (reg).word x i f=0 := by
  have packed : (reg).packed x i f=0:=by
    simp only [fromRAM,dite_eq_right (Nat.not_lt.mpr past)]; rfl
  have empty_:=digit_encode ((encode (reg).field (reg).nodes).symm ((reg).packed x i f)) ((reg).number x)
  simp only [Equiv.apply_symm_apply,packed,Fin.val_zero,digit,Nat.zero_mod,Nat.zero_div] at empty_
  simpa only [Register.word,packed] using empty_.symm

theorem packed_read (x : NodeOrder.All B) (i : Fin l.operands) (f : Fin 3)
    (cells : Fin l.hosts→Fin l.groups→Cell ((fieldBits)*l.nodes))
    (observed : DescentPackedColony.Reads
      (previousBank l a.arguments (block x) (DescentOperandStateBanks.page (page f) i)) cells l.lanes m)
    (fit : (fieldBits)*l.nodes*l.lanes≤w) :
    (reg).packed x i.val f=cells (host x) (groupOf x) := by
  let g:=groupOf x
  let chunk:=physicalChunk pos g
  let row_:Row l.hosts l.groups l.lanes:=(host x,chunk)
  have read:=observed row_
  have size:=(data cells row_).isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) fit)
  have crop : ((m ((previousBank l a.arguments (block x) (DescentOperandStateBanks.page (page f) i)).base+
      (row l.hosts l.groups l.lanes row_).val)).val:Cell (((fieldBits)*l.nodes)*l.lanes))=data cells row_ := by
    apply Fin.ext
    rw [read]
    simp only [Fin.val_natCast,Nat.mod_eq_of_lt size,Nat.mod_eq_of_lt (data cells row_).isLt]
  simp only [fromRAM,i.isLt,dite_eq_left]
  rw [crop]
  simp only [data,Equiv.symm_apply_apply]
  have address : chunk.val*l.lanes+g.val%l.lanes=g.val:=Nat.div_add_mod' _ _
  have inside:=address.trans_lt g.isLt
  exact (dite_eq_left inside).trans (congrArg (cells (host x)) (Fin.ext address))

theorem word_read (x : NodeOrder.All B) (i : Fin l.operands) (f : Fin 3)
    (cells : Fin l.hosts→Fin l.groups→Cell ((fieldBits)*l.nodes))
    (observed : DescentPackedColony.Reads
      (previousBank l a.arguments (block x) (DescentOperandStateBanks.page (page f) i)) cells l.lanes m)
    (fit : (fieldBits)*l.nodes*l.lanes≤w) :
    (reg).word x i.val f=((encode (fieldBits) l.nodes).symm (cells (host x) (groupOf x)) (number x)).val := by
  unfold Register.word
  rw [packed_read a l fieldBits m pos block host groupOf number x i f cells observed fit]; rfl

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
