import OAI.Hierarchy.DescentRangeRegisterCore
import OAI.Hierarchy.DescentPackedNodeDigit

namespace OAI
/-! # The precise SIMD cell read by both a previous-operand lookup and the range archive -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSixParty DescentDatedAddressBook DescentKernelHistory DescentOperandStateBanks
open DescentDatedPriorOperand DescentSIMDLookup DescentPackedColony
open DescentOrdinaryAtomFieldRAM.ScalarOperand Computability.VPVNP.BurstRAM ProtocolRAM
open DescentPackedZip
open scoped Classical Fin.CommRing
noncomputable section

private def alignedChunk {G L : ℕ} (pos : 0<L) (g : Fin G) : Fin (chunks G L) :=
  ⟨g.val/L,by
    change g.val/L<(G+L-1)/L
    apply (Nat.le_div_iff_mul_le pos).2
    rw [Nat.succ_mul]
    have lower:=Nat.div_mul_le_self g.val L
    have upper:=g.isLt
    omega⟩

/-- The physical cell in one of the seven previous-operand pages, at a true host and group. -/
def archivedCell {w : ℕ} (a : PriorResetArchive) (l : Layout) (field : ℕ) (m : Memory w)
    (pos : 0<l.lanes) (p : Pages l.operands) (block : Fin l.blocks)
    (host : Fin l.hosts) (groupOf : Fin l.groups) : Cell (field*l.nodes) :=
  let chunk:=alignedChunk pos groupOf
  let bank:=previousBank l a.arguments block p
  let raw : Cell ((field*l.nodes)*l.lanes):=(m (bank.base+(row l.hosts l.groups l.lanes (host,chunk)).val)).val
  (encode (field*l.nodes) l.lanes).symm raw ⟨groupOf.val%l.lanes,Nat.mod_lt _ pos⟩

/-- Finite readbacks for a produced operand page determine the value of every packed cell. -/
theorem archivedCell_read {w : ℕ} (a : PriorResetArchive) (l : Layout) (field : ℕ) (m : Memory w)
    (pos : 0<l.lanes) (p : Pages l.operands) (b : Fin l.blocks)
    (cells : Fin l.hosts→Fin l.groups→Cell (field*l.nodes))
    (observed : Reads (previousBank l a.arguments b p) cells l.lanes m) (fit : field*l.nodes*l.lanes≤w) :
    archivedCell a l field m pos p b=cells :=by
  funext h g
  let chunk:=alignedChunk pos g
  let row_:Row l.hosts l.groups l.lanes:=(h,chunk)
  have read:=observed row_
  have size:=(data cells row_).isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) fit)
  have crop : (((m ((previousBank l a.arguments b p).base+(row l.hosts l.groups l.lanes row_).val)).val :
      Cell ((field*l.nodes)*l.lanes)))=data cells row_ :=by
    apply Fin.ext
    rw [read]
    simp only [Fin.val_natCast,Nat.mod_eq_of_lt size,Nat.mod_eq_of_lt (data cells row_).isLt]
  change (encode (field*l.nodes) l.lanes).symm
    ((m ((previousBank l a.arguments b p).base+(row l.hosts l.groups l.lanes row_).val)).val :
      Cell ((field*l.nodes)*l.lanes)) ⟨g.val%l.lanes,Nat.mod_lt _ pos⟩=cells h g
  rw [crop]
  simp only [data,Equiv.symm_apply_apply]
  have address : chunk.val*l.lanes+g.val%l.lanes=g.val:=Nat.div_add_mod' _ _
  exact (dite_eq_left (address.trans_lt g.isLt)).trans (congrArg (cells h) (Fin.ext address))

/-- A genuinely produced page can itself be used as the preimage for the next native operand
gather. The original tail padding is certified by the row readback. -/
theorem archivedCell_reads {w : ℕ} (a : PriorResetArchive) (l : Layout) (field : ℕ) (m : Memory w)
    (pos : 0<l.lanes) (p : Pages l.operands) (b : Fin l.blocks) (fit : field*l.nodes*l.lanes≤w)
    (issued : ∃ cells : Fin l.hosts→Fin l.groups→Cell (field*l.nodes),
      Reads (previousBank l a.arguments b p) cells l.lanes m) :
    Reads (previousBank l a.arguments b p) (archivedCell a l field m pos p b) l.lanes m :=by
  obtain ⟨cells,reads⟩:=issued
  rw [archivedCell_read a l field m pos p b cells reads fit]
  exact reads

/-- An argument outside the previous operand rectangle reads as zero. -/
def previousRangeCell {w : ℕ} (a : PriorResetArchive) (l : Layout) (field : ℕ) (m : Memory w)
    (pos : 0<l.lanes) (j : ℕ) (f : Fin 3) (block : Fin l.blocks) (host : Fin l.hosts)
    (groupOf : Fin l.groups) : Cell (field*l.nodes) :=
  if isArg : j<l.operands then
    archivedCell a l field m pos (DescentOperandStateBanks.page (page f) ⟨j,isArg⟩) block host groupOf
  else 0

theorem previousRangeCell_past {w : ℕ} (a : PriorResetArchive) (l : Layout) (field : ℕ) (m : Memory w)
    (pos : 0<l.lanes) {j : ℕ} (past : l.operands≤j) (f : Fin 3)
    (block : Fin l.blocks) (host : Fin l.hosts) (groupOf : Fin l.groups) :
    previousRangeCell a l field m pos j f block host groupOf=0 :=by
  simp [previousRangeCell,Nat.not_lt.mpr past]

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {B : BitDescription W} {w : ℕ} (a : PriorResetArchive) (l : Layout) (field : ℕ)
    (m : Memory w) (pos : 0<l.lanes) (block : NodeOrder.All B→Fin l.blocks)
    (host : NodeOrder.All B→Fin l.hosts) (groupOf : NodeOrder.All B→Fin l.groups) (number : NodeOrder.All B→Fin l.nodes)

theorem word_of_cell (x : NodeOrder.All B) (j : ℕ) (f : Fin 3) :
    (fromRAM a l field m pos block host groupOf number).word x j f =
      (take (number x) (previousRangeCell a l field m pos j f (block x) (host x) (groupOf x))).val :=rfl

include number in
/-- A physical source read identifies this same packed column without requiring every other
field of the predecessor, or reading any proposed next register. -/
theorem cell_of_read (x : NodeOrder.All B) (j : Fin l.operands) (f : Fin 3)
    (cells : Fin l.hosts→Fin l.groups→Cell (field*l.nodes))
    (observed : Reads (previousBank l a.arguments (block x) (DescentOperandStateBanks.page (page f) j)) cells l.lanes m)
    (fit : field*l.nodes*l.lanes≤w) :
    previousRangeCell a l field m pos j.val f (block x) (host x) (groupOf x)=cells (host x) (groupOf x) :=
  packed_read a l field m pos block host groupOf number x j f cells observed fit

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
