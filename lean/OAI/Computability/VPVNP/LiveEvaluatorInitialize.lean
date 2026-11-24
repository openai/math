import OAI.Computability.VPVNP.LiveEvaluatorTail
import OAI.Computability.VPVNP.EvaluatorInputBank
import OAI.Computability.VPVNP.LiveHeaderBits

/-!
# Initial and final words of an evaluator group

At the midpoint the input tape starts at its leftmost input bit, and the
second tape is blank. In the head-relative field the first input bit goes
at cell `M`. A fixed native RAM call reads one packed input bit and stores
its tape symbol. Cells outside the raw input retain their initial zeroes.
The last group's required accepting configuration has state one and zero
in every tape field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorInitialize

open UniversalMachine LiveEvaluatorEncoding

/-- A raw bit is nonblank, including a zero input bit. -/
def bitSymbol (b : Bool) : Symbol := if b then 2 else 1

/-- At cell `i` the head-relative input offset is `i - M`. -/
def inputCell (M : ℕ) (raw : UniversalMachine.Word) (i : ℕ) : Symbol :=
  if i < M then 0 else (raw[i - M]?.map bitSymbol).getD 0

private theorem initial_nth (raw : UniversalMachine.Word) (j : ℤ) :
    (Turing.Tape.mk₁ (raw.map bitSymbol)).nth j =
      if j < 0 then 0 else (raw[j.toNat]?.map bitSymbol).getD 0 := by
  cases j with
  | ofNat n =>
    change (Turing.Tape.mk' _ _).nth (n : ℤ) = _
    rw [Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD, List.getElem?_map]
    simp
  | negSucc n =>
    change (Turing.ListBlank.mk ([] : List Symbol)).nth n = _
    rw [Turing.ListBlank.nth_mk, List.getI_eq_default _ (by simp)]
    rw [ite_eq_left (Int.negSucc_lt_zero n)]
    rfl

theorem initial_firstTape (p : Program) (raw : UniversalMachine.Word) (M : ℕ) (i : Fin (2 * M + 1)) :
    (TapeWindow.ofTape M (initial p raw).firstTape).cells i = inputCell M raw i.val := by
  change (Turing.Tape.mk₁ (raw.map bitSymbol)).nth _ = _
  rw [initial_nth]
  simp [inputCell, show ((i.val : ℤ) - M < 0) ↔ i.val < M by omega,
    show ((i.val : ℤ) - M).toNat = i.val - M by omega]

theorem initial_secondTape (p : Program) (raw : UniversalMachine.Word) (M : ℕ) (i : Fin (2 * M + 1)) :
    (TapeWindow.ofTape M (initial p raw).secondTape).cells i = 0 := by
  change (Turing.Tape.mk₁ (([] : List Bool).map bitSymbol)).nth _ = _
  rw [initial_nth]
  split <;> rfl

/-- The state word is one for the empty table and two for a nonempty
machine, even if it rejects on its first transition. -/
theorem initial_state (p : Program) (raw : UniversalMachine.Word) (M : ℕ) :
    (LiveEvaluatorTail.initialCode M (initial p raw)).stateWord.val =
      if p.extra = 0 then 1 else 2 := by
  by_cases he : p.extra = 0 <;> simp [LiveEvaluatorTail.initialCode, initial, he, Code.stateWord,
    ConfigWindow.ofConfig]

theorem initial_first (p : Program) (raw : UniversalMachine.Word) (M : ℕ) (i : Fin (2 * M + 1)) :
    (LiveEvaluatorTail.initialCode M (initial p raw)).firstCell i =
      if p.extra = 0 then 0 else inputCell M raw i.val := by
  by_cases he : p.extra = 0
  · simp [LiveEvaluatorTail.initialCode, initial, he, Code.firstCell]
  · simpa [LiveEvaluatorTail.initialCode, initial, he, Code.firstCell, ConfigWindow.ofConfig]
      using initial_firstTape p raw M i

theorem initial_second (p : Program) (raw : UniversalMachine.Word) (M : ℕ) (i : Fin (2 * M + 1)) :
    (LiveEvaluatorTail.initialCode M (initial p raw)).secondCell i = 0 := by
  by_cases he : p.extra = 0
  · simp [LiveEvaluatorTail.initialCode, initial, he, Code.secondCell]
  · simpa [LiveEvaluatorTail.initialCode, initial, he, Code.secondCell, ConfigWindow.ofConfig]
      using initial_secondTape p raw M i

/-- Address a field bit by the exact length of all preceding port fields. -/
theorem rawInput_at_field {K : Type} (before after : List K) (k : K) (bank : RAMTape.Stacks K)
    (j : Fin (Evaluator.InputBank.fieldBits (bank k)).length) :
    (Evaluator.InputBank.rawInput (before ++ k :: after) bank)[
      (Evaluator.InputBank.rawInput before bank).length + j.val]? =
      some ((Evaluator.InputBank.fieldBits (bank k))[j.val]) := by
  simp only [Evaluator.InputBank.rawInput, List.flatMap_append, List.flatMap_cons]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left j.isLt, List.getElem?_eq_getElem j.isLt]

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Pack the raw stream in little-endian words. Bits in the last incomplete
word and all words beyond the stream use zero padding. -/
def inputWord (w : ℕ) (raw : UniversalMachine.Word) (row : ℕ) : BurstRAM.Word w :=
  (RAMSerialization.wordBits w).symm (fun i => raw[row * w + i.val]?.getD false)

theorem inputWord_bit (hw : 0 < w) (raw : UniversalMachine.Word) (j : ℕ) :
    (inputWord w raw (j / w)).val.testBit (j % w) = raw[j]?.getD false := by
  let slot : Fin w := ⟨j % w, Nat.mod_lt _ hw⟩
  rw [show j % w = slot.val from rfl, LiveHeader.testBit_wordBits]
  simp [inputWord, slot, Nat.div_add_mod']

/-- Public words give the radius, destination state base, packed raw input
base and word width, in that order. The persistent state is the input bit
number. Register 29 returns the next bit number. -/
def copyBit : List (Op 32 4) :=
  [.constant 1 1, .stateWord 26, .publicWord 11 0, .publicWord 23 1,
    .publicWord 24 2, .publicWord 22 3,
    .binary .div 18 26 22, .binary .mod 19 26 22, .binary .add 20 24 18,
    .read 21 20, .binary .shiftRight 21 21 19, .binary .bitAnd 21 21 1,
    .binary .add 21 21 1, .binary .add 20 23 1, .binary .add 20 20 11,
    .binary .add 20 20 26, .write 20 21, .binary .add 29 26 1]

/-- Store the canonical state word into an otherwise blank bank. The same
native call with tag one prepares the required output at the final group. -/
def putState (tag : BurstRAM.Word 2) : List (Op 32 4) :=
  [.publicWord 23 1, .constant 16 tag, .write 23 16, .stateWord 29]

private theorem wordMod_lt (hw : 0 < w) (n : ℕ) : n % w < 2 ^ w :=
  (Nat.mod_lt n hw).trans (Nat.lt_two_pow_self (n := w))

/-- The address of the packed input word containing the specified input bit. -/
def sourceAddress (pub : Fin 4 → BurstRAM.Word w) (pos : BurstRAM.Word w) :=
  pub 2 + Fin.ofNat (2 ^ w) (pos.val / w)

/-- The first-tape cell receiving an input bit, counting forward from the head in the
serialized configuration. -/
def targetAddress (pub : Fin 4 → BurstRAM.Word w) (pos : BurstRAM.Word w) :=
  pub 1 + 1 + pub 0 + pos

theorem copyBit_trace_replay (hw : 2 ≤ w) (pub : Fin 4 → BurstRAM.Word w) (hwidth : (pub 3).val = w)
    (pos : BurstRAM.Word w) (rs : Regs w 32) (m : Memory w) :
    let bit := (m (sourceAddress pub pos).val).val.testBit (pos.val % w)
    let symbol := PrimedInputRAM.encodeBit w bit + 1
    ∃ es out, trace pub pos copyBit rs m = some (es, out, writeMemory m (targetAddress pub pos) symbol) ∧
      out 29 = pos + 1 ∧ after m es = writeMemory m (targetAddress pub pos) symbol ∧
      es.length = 18 ∧ countProbes es = 2 ∧ choiceBits es = [] ∧ ∀ u, after u es = writeMemory u (targetAddress pub pos) symbol := by
  have hmod := wordMod_lt (by omega : 0 < w) pos.val
  simp (config := { decide := true }) [copyBit, trace, Op.effect, Function.update,
    show BinaryOp.add.eval = (· + · : BurstRAM.Word w → BurstRAM.Word w → BurstRAM.Word w) from rfl,
    show BinaryOp.div.eval = (fun (x y : BurstRAM.Word w) => Fin.ofNat _ (x.val / y.val)) from rfl,
    show BinaryOp.mod.eval = (fun (x y : BurstRAM.Word w) => Fin.ofNat _ (x.val % y.val)) from rfl,
    PrimedInputRAM.Opcodes.readBit_word (by omega : 0 < w), hwidth,
    Nat.mod_eq_of_lt hmod, sourceAddress, targetAddress, after, update, countProbes, choiceBits]

theorem copyBit_trace (hw : 2 ≤ w) (pub : Fin 4 → BurstRAM.Word w) (hwidth : (pub 3).val = w)
    (pos : BurstRAM.Word w) (rs : Regs w 32) (m : Memory w) :
    let bit := (m (sourceAddress pub pos).val).val.testBit (pos.val % w)
    let symbol := PrimedInputRAM.encodeBit w bit + 1
    ∃ es out, trace pub pos copyBit rs m = some (es, out, writeMemory m (targetAddress pub pos) symbol) ∧
      out 29 = pos + 1 ∧ after m es = writeMemory m (targetAddress pub pos) symbol ∧
      es.length = 18 ∧ countProbes es = 2 ∧ choiceBits es = [] := by
  obtain ⟨es, out, run, next, effect, size, probes, bits, _⟩ := copyBit_trace_replay hw pub hwidth pos rs m
  exact ⟨es, out, run, next, effect, size, probes, bits⟩

/-- Native code emits exactly one initialized input symbol with a single
read and write, advancing its persistent cursor. -/
theorem copyBit_native (hw : 2 ≤ w) (pub : Fin 4 → BurstRAM.Word w) (hwidth : (pub 3).val = w)
    (pos : BurstRAM.Word w) (m : Memory w) (raw : UniversalMachine.Word) (hj : pos.val < raw.length)
    (hpack : m (sourceAddress pub pos).val = inputWord w raw (pos.val / w)) :
    let machine := (template copyBit 29).instantiate w pub
    ∃ es, execute machine.program 19 (machine.program.start pos) m [] = some ⟨es, some (pos + 1)⟩ ∧
      after m es = writeMemory m (targetAddress pub pos) (PrimedInputRAM.encodeBit w raw[pos.val] + 1) ∧
      es.length = 18 ∧ countProbes es = 2 ∧ choiceBits es = [] := by
  dsimp only
  obtain ⟨es, out, ht, ho, hm, hl, hp, hb⟩ := copyBit_trace hw pub hwidth pos (fun _ => 0) m
  refine ⟨es, ?_, ?_, hl, hp, hb⟩
  · change execute ((template copyBit 29).instantiate w pub).program (1 + copyBit.length)
      ⟨_,pos,fun _ => 0,fun _ => 0⟩ m [] = _
    rw [execute_template, run_eq_trace, ht]
    simp [ho]
  · simpa [hpack, inputWord_bit (by omega : 0 < w), List.getElem?_eq_getElem hj] using hm

/-- One native write prepares the state field. The full halt-bank contents
are canonical if its tape fields are in zero-default memory. -/
theorem putState_native (pub : Fin 4 → BurstRAM.Word w) (pos : BurstRAM.Word w) (m : Memory w)
    (tag : BurstRAM.Word 2) :
    let machine := (template (putState tag) 29).instantiate w pub
    ∃ es, execute machine.program 5 (machine.program.start pos) m [] = some ⟨es, some pos⟩ ∧
      after m es = writeMemory m (pub 1) (Fin.ofNat _ tag.val) ∧
      es.length = 4 ∧ countProbes es = 1 ∧ choiceBits es = [] := by
  dsimp only
  let es : List (Event w) := [.tick, .tick, .write (pub 1) (Fin.ofNat _ tag.val), .tick]
  refine ⟨es, ?_, rfl, rfl, rfl, rfl⟩
  change execute ((template (putState tag) 29).instantiate w pub).program (1 + (putState tag).length)
      ⟨_,pos,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace]
  simp (config := {decide := true}) [putState, trace, Op.effect, es, Function.update]

end LiveEvaluatorInitialize

end VPVNP
end Computability
end OAI
