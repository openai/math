import OAI.Hierarchy.TaggedPassInputs
import OAI.Hierarchy.TaggedSweep

namespace OAI
/-! # Fixed rectangular scans in the physical digit pass

Every retained scalar slot is read once in increasing order, first from its
local block and then as one lane of a packed word. A read may selectively
ignore any records, in particular dummy rows and all but one digit.
-/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork RadixStage SortedBlock
open scoped Classical
noncomputable section

variable {α : Type*}


namespace PassShape

variable (s : PassShape) {w : ℕ} (dummy : Fin w → Bool)

def blockWord (v : s.LocalData w → Bool) (b : Fin s.blocks) (i : Row s.localBits) :=
  unwrap (fun k => v (b,k)) i

def wideLane (v : s.WideData w → Bool) (r : Row s.globalHeight) (i : Fin s.pack) : Fin w → Bool :=
  fun j => unwrap v r (finProdFinEquiv (i,j))

def retainedIndex (i : Fin s.nextRows) (fits : s.perBlock ≤ 2^s.localBits) : Fin s.blocks × Row s.localBits :=
  let e := finProdFinEquiv.symm (show Fin (s.blocks*s.perBlock) from i)
  (e.1,e.2.castLE fits)

theorem retained_word (fits : s.perBlock ≤ 2^s.localBits) (v : s.LocalData w → Bool)
    (b : Fin s.blocks) (i : Fin s.perBlock) :
    let k := s.retainedIndex (finProdFinEquiv (b,i)) fits
    s.blockWord v k.1 k.2 = s.blockWord v b (i.castLE fits) := by simp [retainedIndex]

theorem enter_block_word (x : RowBits s.rows w → Bool) (b : Fin s.blocks) (i : Row s.localBits) :
    s.blockWord (staticRead (s.enter dummy) x) b i =
      if i.val < s.block then if h : b.val*s.block+i.val < s.rows then fun j => x (⟨_,h⟩,j) else dummy else dummy := by
  funext j
  by_cases inside : i.val < s.block <;> by_cases rowFits : b.val*s.block+i.val < s.rows <;>
    simp [blockWord,unwrap,staticRead,enter,blockScatter,inside,rowFits]

/-- The local-bank scatter is exactly the padded block decomposition of the
original record stream. -/
theorem enter_sweep (x : RowBits s.rows w → Bool) (observe : (Fin w → Bool) → List α)
    (quiet : observe dummy=[]) (fits : s.block ≤ 2^s.localBits) :
    sweep s.blocks (fun b => sweep (2^s.localBits) fun i => observe (s.blockWord (staticRead (s.enter dummy) x) b i)) =
      sweep s.rows (fun i => observe (fun j => x (i,j))) := by
  let physical (i : Fin (s.blocks*s.block)) := if h : i.val < s.rows then observe (fun j => x (⟨i.val,h⟩,j)) else []
  have changeBlock (b : Fin s.blocks) : sweep (2^s.localBits) (fun i => observe (s.blockWord (staticRead (s.enter dummy) x) b i)) =
      sweep s.block (fun i => physical (finProdFinEquiv (b,i))) := by
    apply sweep_extend fits
    · intro i
      rw [enter_block_word]
      simp only [Fin.val_castLE, ite_eq_left i.isLt]
      have ix : (finProdFinEquiv (b,i)).val = b.val*s.block+i.val := by simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
      simp only [physical,ix]; split <;> simp [*]
    · intro i off
      simp [enter_block_word,not_lt.mpr off,quiet]
  simp_rw [changeBlock,←sweep_rect]
  exact sweep_extend s.real_fit _ physical (fun i => dite_eq_left i.isLt) (fun i h => dite_eq_right h.not_gt)

/-- The wide-input wire agrees bit for bit with the quotient/remainder
indexing of a retained slot, and pads only the surplus global slots. -/
theorem wide_word (v : s.LocalData w → Bool) (fits : s.perBlock ≤ 2^s.localBits) (r : Row s.globalHeight) (i : Fin s.pack) :
    s.wideLane (staticRead (s.wideInput dummy) v) r i =
      if h : r.val*s.pack+i.val < s.nextRows then let k := s.retainedIndex ⟨_,h⟩ fits; s.blockWord v k.1 k.2 else dummy := by
  let t := r.val*s.pack+i.val
  have pos : 0 < s.perBlock := (Nat.two_pow_pos (2*s.digitBits)).trans_le (Nat.le_add_right ..)
  have left : t/s.perBlock < s.blocks ↔ t < s.nextRows := by rw [Nat.div_lt_iff_lt_mul pos]; rfl
  have right : t%s.perBlock < 2^s.localBits := (Nat.mod_lt _ pos).trans_le fits
  funext j
  simp only [wideLane,unwrap,staticRead,wideInput,Equiv.symm_apply_apply]
  change (Sum.elim v id (if h : t/s.perBlock < s.blocks ∧ t%s.perBlock < 2^s.localBits then _ else _)) = _
  by_cases h : t < s.nextRows
  · rw [dite_eq_left ⟨left.mpr h,right⟩,dite_eq_left h]
    rfl
  · rw [dite_eq_right (fun k => h (left.mp k.1)),dite_eq_right h]
    rfl

end PassShape
end
end Hierarchy.Tagged.Radix

end OAI
