import OAI.Computability.VPVNP.RAMTapeSortReplaySlot
import OAI.Computability.VPVNP.RAMTapeSortRowModel

/-! # Comparison outcomes and flags on one physical sorting row -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortReplay

open BurstRAM RAMSort RAMMemory RAMBoundary

variable {h d w : ℕ}

/-- Return the operand chosen by a minimum or maximum comparison, with the
same equality convention as the finite comparator. -/
def pick (keepMin : Bool) (a b : OrderedSlot (Word w)) : OrderedSlot (Word w) :=
  if decide (a ≤ b) == keepMin then a else b

theorem parsed_chosen (hw : 2 ≤ w) (keepMin : Bool) (a b : RawSlot w) :
    parsedSlot hw (SortRow.chosen keepMin a b) = pick keepMin (parsedSlot hw a) (parsedSlot hw b) := by
  simp only [SortRow.chosen, Sorter.leDecision_eq hw, pick]
  split <;> rfl

theorem chosen_canonical (hw : 2 ≤ w) (keepMin : Bool) {a b : RawSlot w}
    (ha : Canonical hw a) (hb : Canonical hw b) : Canonical hw (SortRow.chosen keepMin a b) := by
  unfold SortRow.chosen
  split <;> assumption

theorem selectOK_iff (hw : 2 ≤ w) (a b : RawSlot w) :
    SortRow.selectOK a b = true ↔ Canonical hw a ∧ Canonical hw b := by
  simp only [SortRow.selectOK, Bool.and_eq_true, canonical_observed hw]

theorem verifyOK_iff (hw : 2 ≤ w) (a b : RawSlot w) :
    SortRow.verifyOK a b = true ↔ (Canonical hw a ∧ Canonical hw b) ∧ a = b := by
  simp only [SortRow.verifyOK, Bool.and_eq_true, selectOK_iff hw, Sorter.equalDecision_eq, decide_eq_true_eq]

private def rowBit (s : Stage (h+d)) (v : Fin (2^d)) (i : Fin (2^h)) : Bool :=
  let g := v.val*2^h+i.val
  g.testBit s.stride == g.testBit s.phase

private theorem bit_eq (s : Stage (h+d)) (v : Fin (2^d)) (i : Fin (2^h)) :
    (decide ((wireIndex h v.val i.val).eval < (wirePartner h v.val i.val s.stride).eval) ==
      decide ((directionBit h v.val i.val s.phase).eval = 0)) = rowBit s v i := by
  rw [wireIndex_eval, wirePartner_eval, directionBit_eval, orientation]
  rfl

variable (hw : 2 ≤ w) (raw : ℕ → Bool) (s : Stage (h+d)) (v : Fin (2^d))
  (cur : Wires h (OrderedSlot (Word w))) (i : Fin (2^h))

theorem cross_ok (hc : h ≤ s.stride) :
    (scanRow hw raw s v cur i).ok = true ↔
      Canonical hw (fieldWords w raw s 0 i) ∧ Canonical hw (fieldWords w raw s 1 i) ∧
      parsedSlot hw (fieldWords w raw s 0 i) = cur i := by
  simp only [scanRow, hc, dite_true, readSlot_eq, compareSlots_result]
  by_cases ho : Canonical hw (fieldWords w raw s 0 i) <;>
    by_cases hi : Canonical hw (fieldWords w raw s 1 i) <;>
    simp [ho, hi, Bool.and_eq_true]
  rw [ite_eq_left ho, Option.getD_some]
  exact ⟨fun h => ⟨ho,hi,le_antisymm h.1.2 h.2⟩,
    fun h => ⟨⟨⟨ho,hi⟩,h.2.2.le⟩,h.2.2.ge⟩⟩

theorem cross_value (hc : h ≤ s.stride) (hi : Canonical hw (fieldWords w raw s 1 i)) :
    (scanRow hw raw s v cur i).slot =
      pick ((v.val*2^h+i.val).testBit s.stride == (v.val*2^h+i.val).testBit s.phase)
        (cur i) (parsedSlot hw (fieldWords w raw s 1 i)) := by
  simp only [scanRow, hc, dite_true, readSlot_eq]
  change (if (compareSlots _ _).1 == _ then cur i else _) = _
  rw [compareSlots_result, bit_eq, ite_eq_left hi, Option.getD_some]
  rfl

theorem local_ok (hc : s.stride < h) : (scanRow hw raw s v cur i).ok = true := by
  simp [scanRow, Nat.not_le.mpr hc]

theorem local_value (hc : s.stride < h) :
    (scanRow hw raw s v cur i).slot =
      pick ((v.val*2^h+i.val).testBit s.stride == (v.val*2^h+i.val).testBit s.phase)
        (cur i) (cur ⟨partner s.stride i, partner_lt i.isLt hc⟩) := by
  simp only [scanRow, Nat.not_le.mpr hc, dite_false]
  change (if (compareSlots _ _).1 == _ then cur i else _) = _
  rw [compareSlots_result, bit_eq]
  rfl

end RAMTape.SortReplay

end VPVNP
end Computability
end OAI
