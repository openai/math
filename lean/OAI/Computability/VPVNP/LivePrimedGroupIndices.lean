import OAI.Computability.VPVNP.LiveHeaderRuns
import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Preparing the two primed group indices

In Section 14.1, a first-half live group numbered `i` supplies the auxiliary
machine with two little-endian indices. Their low bits are one and zero. The
remaining bits represent `i - 1` and `i`. Each digit call propagates a
single borrow through external scratch, even when the index exceeds a RAM word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader.PrimedGroupIndices

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- The borrow entering digit `j` in the subtraction `i - 1`. -/
def borrow (i : ℕ) : ℕ → Bool
  | 0 => true
  | j + 1 => borrow i j && !i.testBit j

private theorem borrow_quotient {i : ℕ} (hi : 0 < i) (j : ℕ) :
    i / 2^j = (i - 1) / 2^j + (borrow i j).toNat := by
  induction j with
  | zero => simp [borrow]; omega
  | succ j ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, borrow]
    cases h : borrow i j <;> cases b : i.testBit j <;>
      simp [Nat.testBit_eq_decide_div_mod_eq] at b <;> simp [h] at ih ⊢ <;> omega

private theorem pred_digit {i : ℕ} (hi : 0 < i) (j : ℕ) :
    (i - 1).testBit j = (i.testBit j ^^ borrow i j) := by
  have hq := borrow_quotient hi j
  cases h : borrow i j <;> cases b : i.testBit j <;>
    simp [h] at hq <;> simp [Nat.testBit_eq_decide_div_mod_eq] at b ⊢ <;> omega

private theorem shifted_digits {i : ℕ} (hi : 0 < i) (j : ℕ) :
    (2*i-1).testBit (j+1) = (i-1).testBit j ∧ (2*i).testBit (j+1) = i.testBit j := by
  have hl : 2*i-1 = Nat.bit true (i-1) := by simp [Nat.bit]; omega
  have hr : 2*i = Nat.bit false i := by simp [Nat.bit]
  rw [hl, hr, Nat.testBit_bit_succ, Nat.testBit_bit_succ]
  trivial

/-- In the last group the scanned low digits are all zero and subtraction
still carries its borrow. In every earlier group the borrow has cleared. -/
theorem borrow_endpoint {i h : ℕ} (hi : 0 < i) (hle : i ≤ 2^h) :
    borrow i h = decide (i = 2^h) := by
  have q := borrow_quotient hi h
  rw [Nat.div_eq_of_lt (by omega : i - 1 < 2^h), Nat.zero_add] at q
  by_cases he : i = 2^h
  · subst i
    rw [Nat.div_self (Nat.two_pow_pos h)] at q
    cases hb : borrow (2^h) h
    · simp [hb] at q
    · simp
  · rw [Nat.div_eq_of_lt (by omega : i < 2^h)] at q
    cases hb : borrow i h
    · simp [he]
    · simp [hb] at q

/-- Public words give the input base, left and right output bases, and the
borrow address. The initialization sets both low bits and starts the borrow. -/
def setup : List (Op 12 4) :=
  [.constant 0 0, .constant 1 1, .publicWord 2 1, .publicWord 3 2, .publicWord 4 3,
   .write 2 1, .write 3 0, .write 4 1]

/-- Set the low bits of the left and right primed indices to one and zero and initialize the
borrow for subtracting one from the live group index. -/
def initialized (pub : Fin 4 → Word w) (m : Memory w) : Memory w :=
  writeMemory (writeMemory (writeMemory m (pub 1) 1) (pub 2) 0) (pub 3) 1

/-- Both reads precede the three writes. Register 9 receives the new
borrow, register 10 the bit of the predecessor, and register 11 the next cursor. -/
def digit : List (Op 12 4) :=
  [.stateWord 0, .constant 1 1, .binary .add 11 0 1,
   .publicWord 2 0, .binary .add 2 2 0, .read 5 2,
   .publicWord 3 1, .binary .add 3 3 11, .publicWord 4 2, .binary .add 4 4 11,
   .publicWord 6 3, .read 7 6,
   .binary .sub 9 1 5, .binary .mul 9 9 7,
   .binary .sub 10 5 7, .binary .add 10 10 9, .binary .add 10 10 9,
   .write 3 10, .write 4 5, .write 6 9]

/-- Store the next digits of the two primed indices, using the incoming borrow for the left
digit, and propagate the new borrow. -/
def updated (pub : Fin 4 → Word w) (state : Word w) (m : Memory w) (x c : Bool) : Memory w :=
  let m₁ := writeMemory m (pub 1 + (state + 1)) (encodeBit w (x ^^ c))
  let m₂ := writeMemory m₁ (pub 2 + (state + 1)) (encodeBit w x)
  writeMemory m₂ (pub 3) (encodeBit w (c && !x))

private theorem borrowWord (x c : Bool) :
    (1 - encodeBit w x) * encodeBit w c = encodeBit w (c && !x) := by
  cases x <;> cases c <;> simp [encodeBit]

private theorem predWord (x c : Bool) :
    encodeBit w x - encodeBit w c + encodeBit w (c && !x) + encodeBit w (c && !x) =
      encodeBit w (x ^^ c) := by
  cases x <;> cases c <;> simp [encodeBit]

/-- A native initialization call takes three probes and returns cursor zero. -/
theorem initialize_native (pub : Fin 4 → Word w) (state : Word w) (m : Memory w) :
    let machine := (template setup 0).instantiate w pub
    ∃ es, execute machine.program 9 (machine.program.start state) m [] = some ⟨es, some 0⟩ ∧
      after m es = initialized pub m ∧ es.length = 8 ∧ countProbes es = 3 ∧ choiceBits es = [] := by
  dsimp only
  let es : List (Event w) := [.tick, .tick, .tick, .tick, .tick, .write (pub 1) 1,
    .write (pub 2) 0, .write (pub 3) 1]
  refine ⟨es, ?_, rfl, rfl, rfl, rfl⟩
  change execute ((template setup 0).instantiate w pub).program (1 + setup.length)
    ⟨_,state,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace]
  simp (config := { decide := true }) [setup, trace, Op.effect, Function.update, es]

/-- Executing the same fixed table at every digit takes five probes. -/
theorem digit_native (pub : Fin 4 → Word w) (state : Word w) (m : Memory w) (x c : Bool)
    (hx : m (pub 0 + state).val = encodeBit w x) (hc : m (pub 3).val = encodeBit w c) :
    let machine := (template digit 11).instantiate w pub
    ∃ es, execute machine.program 21 (machine.program.start state) m [] =
        some ⟨es, some (state + 1)⟩ ∧
      after m es = updated pub state m x c ∧ es.length = 20 ∧ countProbes es = 5 ∧ choiceBits es = [] := by
  dsimp only
  let es : List (Event w) := [.tick, .tick, .tick, .tick, .tick, .read (pub 0 + state) (encodeBit w x),
    .tick, .tick, .tick, .tick, .tick, .read (pub 3) (encodeBit w c), .tick, .tick, .tick, .tick, .tick,
    .write (pub 1 + (state + 1)) (encodeBit w (x ^^ c)), .write (pub 2 + (state + 1)) (encodeBit w x),
    .write (pub 3) (encodeBit w (c && !x))]
  refine ⟨es, ?_, rfl, rfl, rfl, rfl⟩
  change execute ((template digit 11).instantiate w pub).program (1 + digit.length)
    ⟨_,state,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace]
  simp (config := { decide := true }) [digit, trace, Op.effect, Function.update, es, hx, hc,
    show BinaryOp.add.eval = (· + · : Word w → Word w → Word w) from rfl,
    show BinaryOp.sub.eval = (· - · : Word w → Word w → Word w) from rfl,
    show BinaryOp.mul.eval = (· * · : Word w → Word w → Word w) from rfl, borrowWord, predWord]

/-- Addresses outside both output arrays and the scalar borrow cell. -/
def outside (pub : Fin 4 → Word w) (h a : ℕ) : Prop :=
  a ≠ (pub 3).val ∧ (a < (pub 1).val ∨ (pub 1).val + h < a) ∧
    (a < (pub 2).val ∨ (pub 2).val + h < a)

/-- All array addresses fit and writable regions are disjoint. Bases can
occur in any physical order, and unrelated scratch may surround them. -/
structure Layout (pub : Fin 4 → Word w) (h : ℕ) : Prop where
  inputFit : (pub 0).val + h ≤ 2^w
  leftFit : (pub 1).val + h < 2^w
  rightFit : (pub 2).val + h < 2^w
  outputsApart : (pub 1).val + h < (pub 2).val ∨ (pub 2).val + h < (pub 1).val
  borrowLeft : (pub 3).val < (pub 1).val ∨ (pub 1).val + h < (pub 3).val
  borrowRight : (pub 3).val < (pub 2).val ∨ (pub 2).val + h < (pub 3).val
  inputOutside : ∀ j < h, outside pub h ((pub 0).val + j)

/-- Each address holds one unpacked bit of a little-endian integer. -/
def stores (m : Memory w) (base : Word w) (width n : ℕ) : Prop :=
  ∀ j < width, m (base.val + j) = encodeBit w (n.testBit j)

/-- Read an unpacked array as a little-endian bit string. -/
def storedBits (m : Memory w) (base : Word w) (width : ℕ) : List Bool :=
  List.ofFn fun j : Fin width => (m (base.val + j.val)).val.testBit 0

private theorem encodeBit_low (hw : 0 < w) (b : Bool) : (encodeBit w b).val.testBit 0 = b := by
  cases b <;> simp [encodeBit, Nat.testBit_eq_decide_div_mod_eq,
    Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')]

/-- The decoded value uses arbitrary natural-number precision, independently of
the width of a single RAM word. -/
theorem stores_value (hw : 0 < w) {m : Memory w} {base : Word w} {width n : ℕ}
    (fit : n < 2^width) (hs : stores m base width n) :
    PrimedCounter.GuessWord.value (storedBits m base width) = n := by
  let v : Word width := ⟨n, fit⟩
  have he : storedBits m base width = wordBits v := by
    apply congrArg List.ofFn
    funext j
    rw [hs j.val j.isLt, encodeBit_low hw]
    exact testBit_wordBits v j
  rw [he, PrimedCounter.GuessWord.value_wordBits]

/-- Both output integers fit even when doubling sets a new high bit. -/
theorem pair_values (hw : 0 < w) {m : Memory w} {left right : Word w} {h i : ℕ}
    (fit : i < 2^h) (hl : stores m left (h+1) (2*i-1)) (hr : stores m right (h+1) (2*i)) :
    PrimedCounter.GuessWord.value (storedBits m left (h+1)) = 2*i-1 ∧
    PrimedCounter.GuessWord.value (storedBits m right (h+1)) = 2*i :=
  ⟨stores_value hw (by rw [pow_succ]; omega) hl, stores_value hw (by rw [pow_succ]; omega) hr⟩

/-- After processing `j` digits, the two output prefixes store the low `j + 1` bits of `2*i -
1` and `2*i`, the borrow cell is current, and memory outside the workspace agrees with its
initial contents. -/
structure Invariant (pub : Fin 4 → Word w) (i h j : ℕ) (original m : Memory w) : Prop where
  borrowCell : m (pub 3).val = encodeBit w (borrow i j)
  left : stores m (pub 1) (j+1) (2*i-1)
  right : stores m (pub 2) (j+1) (2*i)
  frame : ∀ a, outside pub h a → m a = original a

theorem invariant_zero (pub : Fin 4 → Word w) {i h : ℕ} (hi : 0 < i)
    (layout : Layout pub h) (m : Memory w) : Invariant pub i h 0 m (initialized pub m) := by
  have hLR := layout.outputsApart
  have hBL := layout.borrowLeft
  have hBR := layout.borrowRight
  have hlow : (2*i-1).testBit 0 = true := by simp [Nat.testBit_eq_decide_div_mod_eq]; omega
  have hzero : (2*i).testBit 0 = false := by simp [Nat.testBit_eq_decide_div_mod_eq]
  refine ⟨by simp [initialized, writeMemory, borrow, encodeBit], ?_, ?_, ?_⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp [initialized, writeMemory, show (pub 1).val ≠ (pub 3).val by omega,
      show (pub 1).val ≠ (pub 2).val by omega, hlow, encodeBit]
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp [initialized, writeMemory, show (pub 2).val ≠ (pub 3).val by omega, hzero, encodeBit]
  · rintro a ⟨hb, hl, hr⟩
    simp [initialized, writeMemory, hb, show a ≠ (pub 1).val by omega, show a ≠ (pub 2).val by omega]

theorem offset_val (base : Word w) (j : ℕ) (hj : base.val + j < 2^w) :
    (base + (j : Word w)).val = base.val + j := by
  rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (show j < 2^w by omega), Nat.mod_eq_of_lt hj]

theorem invariant_succ (pub : Fin 4 → Word w) {i h j : ℕ} (hi : 0 < i)
    (layout : Layout pub h) (hj : j < h) {m₀ m : Memory w} (inv : Invariant pub i h j m₀ m) :
    Invariant pub i h (j+1) m₀ (updated pub (j : Word w) m (i.testBit j) (borrow i j)) := by
  have hLR := layout.outputsApart
  have hBL := layout.borrowLeft
  have hBR := layout.borrowRight
  have hL := layout.leftFit
  have hR := layout.rightFit
  have lval : (pub 1 + ((j : Word w) + 1)).val = (pub 1).val + (j+1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using offset_val (pub 1) (j+1) (by omega)
  have rval : (pub 2 + ((j : Word w) + 1)).val = (pub 2).val + (j+1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using offset_val (pub 2) (j+1) (by omega)
  have ⟨left, right⟩ := shifted_digits hi j
  rw [pred_digit hi] at left
  refine ⟨by simp [updated, writeMemory, borrow], ?_, ?_, ?_⟩
  · intro k hk
    simp only [updated, writeMemory, lval, rval, show (pub 1).val + k ≠ (pub 3).val by omega,
      show (pub 1).val + k ≠ (pub 2).val + (j+1) by omega, ↓reduceIte, Nat.add_left_cancel_iff]
    by_cases hkj : k = j+1
    · simp [hkj, left]
    · simpa [hkj] using inv.left k (by omega)
  · intro k hk
    simp only [updated, writeMemory, lval, rval, show (pub 2).val + k ≠ (pub 3).val by omega,
      show (pub 2).val + k ≠ (pub 1).val + (j+1) by omega, ↓reduceIte, Nat.add_left_cancel_iff]
    by_cases hkj : k = j+1
    · simp [hkj, right]
    · simpa [hkj] using inv.right k (by omega)
  · intro a ha
    obtain ⟨hb, hl, hr⟩ := ha
    simpa [updated, writeMemory, lval, rval, hb, show a ≠ (pub 1).val + (j+1) by omega,
      show a ≠ (pub 2).val + (j+1) by omega] using inv.frame a ⟨hb, hl, hr⟩

/-- One setup call followed by `h` deterministic digit calls gives the exact
`h+1` output bits, clears the borrow, and preserves every other memory cell.
For the middle live group the right array includes the high bit of `L`. -/
theorem native (pub : Fin 4 → Word w) (h i : ℕ) (hi : 0 < i) (fit : i < 2^h)
    (layout : Layout pub h) (state : Word w) (m : Memory w) (input : stores m (pub 0) h i) :
    let init := (template setup 0).instantiate w pub
    let P := ((template digit 11).instantiate w pub).program
    ∃ es rs, execute init.program 9 (init.program.start state) m [] = some ⟨es, some 0⟩ ∧
      countProbes es = 3 ∧
      runSegment P 21 (some 0) (after m es) (List.replicate h []) = some rs ∧
      endState (some 0) rs = some (h : Word w) ∧ rs.length = h ∧
      (∀ r ∈ rs, countProbes r.events ≤ 5) ∧
      let out := after (after m es) (eventLog rs)
      stores out (pub 1) (h+1) (2*i-1) ∧ stores out (pub 2) (h+1) (2*i) ∧
        out (pub 3).val = 0 ∧ ∀ a, outside pub h a → out a = m a := by
  dsimp only
  obtain ⟨es, he, hm, _, hp, _⟩ := initialize_native pub state m
  have hz := invariant_zero pub hi layout m
  obtain ⟨rs, hs, hend, inv, hlen, probes⟩ := run_cursor_segment
    ((template digit 11).instantiate w pub).program 21 h 5
    (fun j mem => Invariant pub i h j m mem) (initialized pub m) hz (by
      intro j hj mem hjmem
      have addr := offset_val (pub 0) j (by have := layout.inputFit; omega)
      have hx : mem (pub 0 + (j : Word w)).val = encodeBit w (i.testBit j) := by
        rw [addr, hjmem.frame _ (layout.inputOutside j hj), input j hj]
      obtain ⟨fs, hf, hm', _, hp', _⟩ := digit_native pub (j : Word w) mem _ _ hx hjmem.borrowCell
      refine ⟨fs, by simpa only [Nat.cast_add, Nat.cast_one] using hf, ?_, hp'.le⟩
      rw [hm']
      exact invariant_succ pub hi layout hj hjmem)
  have hb : borrow i h = false := by
    have q := borrow_quotient hi h
    rw [Nat.div_eq_of_lt fit, Nat.div_eq_of_lt (by omega)] at q
    cases hh : borrow i h
    · rfl
    · simp [hh] at q
  refine ⟨es, rs, he, hp, ?_⟩
  rw [hm]
  exact ⟨hs, hend, hlen, probes, inv.left, inv.right,
    by simpa [hb, encodeBit] using inv.borrowCell, inv.frame⟩

end LiveHeader.PrimedGroupIndices

end VPVNP
end Computability
end OAI
