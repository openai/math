import OAI.Hierarchy.ProtocolRAMScan
import OAI.Hierarchy.ProbeFeed

namespace OAI
/-! # Integer reserve feeds on the advised native tape -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing BigOperators

variable {w : ℕ}

/-- All intervals share the same allocation table. Each row is indexed by the
actual reserve at the beginning of the feed, before any of its bits were delivered. -/
def feedAdvice (bank : Bank) (steps stride : ℕ) (m : Memory w) : Memory w :=
  fillSegment bank.base (steps*stride) (fun a =>
    let pos := a - bank.base
    (AdaptiveProbe.slice steps (pos%stride) (pos/stride) : Word w)) m

def feed (bank : Bank) (stride mesh : ℕ) (reserve stock : Expr) : Expr :=
  .op .add stock (.lookup bank (.op .add (.lit (mesh*stride)) reserve))

theorem feed_table (bank : Bank) (steps stride : ℕ) (i : Fin steps) (b : Fin stride) (m : Memory w)
    (size : steps*stride ≤ bank.size) (limit : steps*stride<2^w) :
    bank.read (feedAdvice bank steps stride m) ((i.val*stride+b.val : ℕ):Word w) =
      (AdaptiveProbe.slice steps b.val i.val : Word w) := by
  have hb := b.isLt
  have hi := i.isLt
  have next : (i.val+1)*stride ≤ steps*stride := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at next
  have pos : i.val*stride+b.val < steps*stride := by omega
  have inside : bank.base ≤ bank.base+(i.val*stride+b.val) ∧
      bank.base+(i.val*stride+b.val)<bank.base+steps*stride := by omega
  have quo : (i.val*stride+b.val)/stride=i.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hb,Nat.zero_add]
  have rem : (i.val*stride+b.val)%stride=b.val := Nat.mul_add_mod_of_lt hb
  simp only [Bank.read,Fin.val_cast_of_lt (pos.trans limit),Nat.mod_eq_of_lt (pos.trans_le size),
    feedAdvice,fillSegment,ite_eq_left inside,Nat.add_sub_cancel_left,quo,rem]

theorem feed_readback (bank : Bank) (stride steps mesh bits old : ℕ)
    (reserve stock : Expr) (m : Memory w) (r : Word w)
    (saved : reserve.eval m r = (bits : Word w)) (previous : stock.eval m r = (old:Word w))
    (entry : bank.read m ((mesh*stride+bits:ℕ):Word w) = (AdaptiveProbe.slice steps bits mesh : Word w)) :
    (feed bank stride mesh reserve stock).eval m r = ((old+AdaptiveProbe.slice steps bits mesh : ℕ):Word w) := by
  simp only [Nat.cast_add,Nat.cast_mul] at entry
  simp [feed,Expr.eval,RowOp.opcode,BinaryOp.eval,saved,previous,Nat.cast_add,entry]

/-- Even for reserves smaller than the number of intervals, the native feed entries
return precisely the original number of bits in total. -/
theorem feed_sum (bank : Bank) (steps stride : ℕ) (b : Fin stride) (m : Memory w) (h : 0<steps)
    (size : steps*stride≤bank.size) (limit : steps*stride<2^w) :
    ∑ i : Fin steps, bank.read (feedAdvice bank steps stride m) ((i.val*stride+b.val:ℕ):Word w) =
      (b.val : Word w) := by
  simp only [feed_table bank steps stride _ b m size limit,←Nat.cast_sum]
  apply congrArg (fun z : ℕ => (z : Word w))
  simpa [Fin.sum_univ_eq_sum_range] using AdaptiveProbe.slice_sum steps b.val h


end Hierarchy.ProtocolRAM

end OAI
