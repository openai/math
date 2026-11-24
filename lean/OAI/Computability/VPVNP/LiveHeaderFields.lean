import OAI.Computability.VPVNP.LiveHeaderBits

/-!
# Copying payload and validating zero padding in a live cut

An incoming or outgoing cut bit resides in the packed header of the processor
at its cut offset. The offset of a payload field can depend on the distributed
group index. A descriptor word supplies that offset. The destination array is
fixed across groups, including for the two exponent buffers and tail configurations.
Each call checks or copies one bit and advances its persistent cursor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Public slots are the phase's first cursor, the address of the source
offset descriptor, and the fixed base of the destination array. Register 4
holds the absolute cursor, register 5 the position within this field. -/
def locateCell (slot : Fin 4) : List (Op 12 3) :=
  [.stateWord 4, .publicWord 6 0, .binary .sub 5 4 6,
    .publicWord 6 1, .read 6 6, .binary .add 0 6 5] ++ fetch slot

/-- Copy one bit to the same offset in the designated unpacked field. -/
def copyFieldCell (slot : Fin 4) : List (Op 12 3) :=
  locateCell slot ++ [.publicWord 6 2, .binary .add 6 6 5, .write 6 1, .binary .add 7 4 3]

/-- Reject a nonzero padding bit. This same guard checks all nonmode bits
of an incident cut in unit mode. -/
def checkPaddingCell (slot : Fin 4) : List (Op 12 3) :=
  locateCell slot ++ [.constant 6 0, .guardEq 1 6, .binary .add 7 4 3]

/-- The packed-header source address found by adding the current field-relative cursor to the
offset read from the descriptor. -/
def sourceSite (pub : Fin 3 → Word w) (state : Word w) (m : Memory w) : Word w :=
  m (pub 1).val + (state - pub 0)

theorem copyFieldCell_trace (hw : 4 ≤ w) (slot : Fin 4) (pub : Fin 3 → Word w)
    (state : Word w) (rs : Regs w 12) (m : Memory w) :
    let dst := pub 2 + (state - pub 0)
    let v := m (sourceSite pub state m).val
    let b := PrimedInputRAM.encodeBit w (v.val.testBit slot.val)
    ∃ es rs', trace pub state (copyFieldCell slot) rs m = some (es, rs', writeMemory m dst b) ∧
      rs' 7 = state + 1 ∧ es.length = 15 ∧ countProbes es = 3 ∧ choiceBits es = [] := by
  have hlt : slot.val < 2 ^ w := slot.isLt.trans_le (show 4 ≤ 2^w from by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hw; norm_num at this; omega)
  simp (config := { decide := true }) [copyFieldCell, locateCell, fetch, trace, Op.effect, Function.update,
    show BinaryOp.add.eval = (· + · : Word w → Word w → Word w) from rfl,
    show BinaryOp.sub.eval = (· - · : Word w → Word w → Word w) from rfl,
    PrimedInputRAM.Opcodes.readBit_word (by omega : 0 < w), Nat.mod_eq_of_lt hlt,
    sourceSite, countProbes, choiceBits]

theorem checkPaddingCell_trace (hw : 4 ≤ w) (slot : Fin 4) (pub : Fin 3 → Word w)
    (state : Word w) (rs : Regs w 12) (m : Memory w) :
    if (m (sourceSite pub state m).val).val.testBit slot.val then
      trace pub state (checkPaddingCell slot) rs m = none
    else ∃ es rs', trace pub state (checkPaddingCell slot) rs m = some (es, rs', m) ∧
      rs' 7 = state + 1 ∧ es.length = 14 ∧ countProbes es = 2 ∧ choiceBits es = [] := by
  have hlt : slot.val < 2 ^ w := slot.isLt.trans_le (show 4 ≤ 2^w from by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hw; norm_num at this; omega)
  have hone : (1 : Word w) ≠ 0 := by
    rw [ne_eq, Fin.ext_iff]
    have h := Nat.one_lt_two_pow (by omega : w ≠ 0)
    simp [Nat.mod_eq_of_lt h]
  unfold sourceSite
  cases hb : (m (m (pub 1).val + (state - pub 0)).val).val.testBit slot.val <;>
    simp (config := { decide := true }) [checkPaddingCell, locateCell, fetch, trace, Op.effect,
      Function.update, show BinaryOp.add.eval = (· + · : Word w → Word w → Word w) from rfl,
      show BinaryOp.sub.eval = (· - · : Word w → Word w → Word w) from rfl,
      PrimedInputRAM.Opcodes.readBit_word (by omega : 0 < w), Nat.mod_eq_of_lt hlt,
      hb, PrimedInputRAM.encodeBit, hone, countProbes, choiceBits]

/-- For the real packed header at the computed site, the padding microcall
has a successful native return exactly when the designated field bit is zero. -/
theorem checkPaddingCell_native_iff (hw : 4 ≤ w) (slot : Fin 4) (pub : Fin 3 → Word w)
    (state : Word w) (m : Memory w) (h : ProcessorInput.Header)
    (hm : m (sourceSite pub state m).val = ProcessorInput.headerWord hw h) :
    let machine := (template (checkPaddingCell slot) 7).instantiate w pub
    (execute machine.program 15 (machine.program.start state) m []).isSome = true ↔ h slot = false := by
  dsimp only
  change (execute ((template (checkPaddingCell slot) 7).instantiate w pub).program
    (1 + (checkPaddingCell slot).length) ⟨_,state,fun _ => 0,fun _ => 0⟩ m []).isSome = true ↔ _
  rw [execute_template, run_eq_trace]
  have ht := checkPaddingCell_trace hw slot pub state (fun _ => 0) m
  have hbit : (m (sourceSite pub state m).val).val.testBit slot.val = h slot := by
    rw [hm, show slot.val = (slot.castLE hw).val from rfl, testBit_wordBits, ProcessorInput.headerWord_bit]
  rw [hbit] at ht
  cases he : h slot with
  | false =>
    simp only [he, Bool.false_eq_true, ↓reduceIte] at ht
    obtain ⟨es, rs, ht, _⟩ := ht
    simp [ht]
  | true =>
    simp only [he, ↓reduceIte] at ht
    simp [ht]

end LiveHeader

end VPVNP
end Computability
end OAI
