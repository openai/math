import OAI.Computability.VPVNP.PrimedInputRAMOpcodeFields
import OAI.Computability.VPVNP.RAMSiteInput

/-!
# Native reads of the distributed live header

One processor location stores its four local header bits in the low end of
one external word. A microcall addresses a single site, extracts a statically
chosen field, and stores one bit in a separate scratch array. The cursor and
the array base are words, independently of the distributed index length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

theorem testBit_wordBits (x : Word w) (i : Fin w) :
    x.val.testBit i.val = RAMSerialization.wordBits w x i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change decide (x.val / 2 ^ i.val % 2 = 1) = (finFunctionFinEquiv.symm x i == 1)
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, Fin.ext_iff, finFunctionFinEquiv_symm_apply_val]
  rfl

theorem extract_packed_bit (hw : 4 ≤ w) (h : ProcessorInput.Header) (slot : Fin 4) :
    BinaryOp.bitAnd.eval (BinaryOp.shiftRight.eval (ProcessorInput.headerWord hw h)
      (Fin.ofNat _ slot.val)) 1 = PrimedInputRAM.encodeBit w (h slot) := by
  have hlt : slot.val < 2^w := slot.isLt.trans_le (show 4 ≤ 2^w from by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hw; norm_num at this; omega)
  rw [PrimedInputRAM.Opcodes.readBit_word (by omega), Fin.val_ofNat, Nat.mod_eq_of_lt hlt]
  rw [show slot.val = (slot.castLE hw).val from rfl, testBit_wordBits, ProcessorInput.headerWord_bit]

/-- A slot extractor. Register 0 holds the site address. Register 1 receives
the bit word. The scratch registers are 2 and 3. -/
def fetch (slot : Fin 4) {k : ℕ} : List (Op 12 k) :=
  [.read 1 0, .constant 2 slot, .binary .shiftRight 1 1 2, .constant 3 1, .binary .bitAnd 1 1 3]

/-- Copy one field of the processor at `state - pub 0` to the same offset in
the scratch array beginning at `pub 1`, and advance the persistent cursor.
This is a constant instruction list at every input length. -/
def copyCell (slot : Fin 4) : List (Op 12 2) :=
  [.stateWord 4, .publicWord 5 0, .binary .sub 0 4 5] ++ fetch slot ++
    [.publicWord 6 1, .binary .add 6 6 0, .write 6 1, .binary .add 7 4 3]

/-- The exact interpreter trace of a copy call, on arbitrary external memory. -/
theorem copyCell_trace (hw : 4 ≤ w) (slot : Fin 4) (pub : Fin 2 → Word w)
    (state : Word w) (rs : Regs w 12) (m : Memory w) :
    let addr := state - pub 0
    let dst := pub 1 + addr
    let v := m addr.val
    let b := PrimedInputRAM.encodeBit w (v.val.testBit slot.val)
    ∃ es rs', trace pub state (copyCell slot) rs m = some (es, rs', writeMemory m dst b) ∧
      rs' 7 = state + 1 ∧ es.length = 12 ∧ countProbes es = 2 ∧ choiceBits es = [] := by
  have hlt : slot.val < 2 ^ w := slot.isLt.trans_le (show 4 ≤ 2^w from by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hw; norm_num at this; omega)
  simp (config := { decide := true }) [copyCell, fetch, trace, Op.effect, Function.update,
    show BinaryOp.add.eval = (· + · : Word w → Word w → Word w) from rfl,
    show BinaryOp.sub.eval = (· - · : Word w → Word w → Word w) from rfl,
    PrimedInputRAM.Opcodes.readBit_word (by omega : 0 < w),
    Nat.mod_eq_of_lt hlt, countProbes, choiceBits]

/-- A correctly packed header is copied to the unpacked destination array as a
single bit. The native program takes two probes and returns the next cursor. -/
theorem copyCell_native (hw : 4 ≤ w) (slot : Fin 4) (pub : Fin 2 → Word w)
    (state : Word w) (m : Memory w) (h : ProcessorInput.Header)
    (hm : m (state - pub 0).val = ProcessorInput.headerWord hw h) :
    let dst := pub 1 + (state - pub 0)
    let machine := (template (copyCell slot) 7).instantiate w pub
    ∃ es, execute machine.program 13 (machine.program.start state) m [] = some ⟨es, some (state + 1)⟩ ∧
      after m es = writeMemory m dst (PrimedInputRAM.encodeBit w (h slot)) ∧
      es.length = 12 ∧ countProbes es = 2 ∧ choiceBits es = [] := by
  dsimp only
  let addr := state - pub 0
  obtain ⟨es, rs, ht, hr, hl, hp, hc⟩ := copyCell_trace hw slot pub state (fun _ => 0) m
  have hbit : (m addr.val).val.testBit slot.val = h slot := by
    change (m (state - pub 0).val).val.testBit (slot.castLE hw).val = h slot
    rw [hm, testBit_wordBits, ProcessorInput.headerWord_bit]
  refine ⟨es, ?_, ?_, hl, hp, hc⟩
  · change execute ((template (copyCell slot) 7).instantiate w pub).program (1 + (copyCell slot).length)
      ⟨_,state,fun _ => 0,fun _ => 0⟩ m [] = _
    rw [execute_template, run_eq_trace, ht]
    simp [hr]
  · have hd : after m es = writeMemory m (pub 1 + addr)
        (PrimedInputRAM.encodeBit w ((m addr.val).val.testBit slot.val)) := by
      simp (config := { decide := true }) [copyCell, fetch, trace, Op.effect, Function.update] at ht
      rw [← ht.1]
      exact ht.2.2
    rwa [hbit] at hd

end LiveHeader

end VPVNP
end Computability
end OAI
