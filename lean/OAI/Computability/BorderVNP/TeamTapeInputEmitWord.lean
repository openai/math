import OAI.Computability.BorderVNP.TeamTapeSortingRecords
import OAI.Computability.VPVNP.RAMTapeRecordBuffer
import OAI.Computability.VPVNP.RAMTapeWordOperands
import OAI.Computability.VPVNP.RAMTapeUnaryWordValue
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-! # Word staging for consecutive time-zero team records

The finite word scanner restores its source and overwrites its destination. Copy, increment,
fixed literals and a left shift with a specified low bit suffice to form the five words of
a read or write half and advance the current address. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputEmit

open VPVNP BurstRAM RAMTape TapeWord

/-- The unread input, the running address, and the physical record buffer. -/
inductive Port where
  | bits | cursor | buffer (p : RecordBuffer.Port)
  deriving DecidableEq, Fintype

/-- A staging scan copies the cursor to a field, or advances it from the last address field. -/
inductive Move where
  | stage (j : Fin 5) | advance

/-- Source of the scan. -/
def Move.src : Move → Port
  | .stage _ => .cursor
  | .advance => .buffer (.field 1)

/-- Destination overwritten by the scan. -/
def Move.dst : Move → Port
  | .stage j => .buffer (.field j)
  | .advance => .cursor

private def ports (m : Move) : ScanPort → Port
  | .left => m.src
  | .right => .buffer .temp
  | .tmp => .buffer .output
  | .out => m.dst

private theorem ports_inj (m : Move) : Function.Injective (ports m) := by
  intro i j h
  cases m <;> cases i <;> cases j <;> simp_all [ports, Move.src, Move.dst]

/-- Word transformations in the two initialization records and the address counter. -/
inductive Op where
  | copy | literal (n : ℕ) | double (phase : Bool) | increment

/-- Numeric interpretation; taking the word residue implements fixed-width arithmetic. -/
def Op.eval (op : Op) (a : ℕ) : ℕ :=
  match op with
  | .copy => a
  | .literal n => n
  | .double p => 2*a+p.toNat
  | .increment => a+1

private def normal {A : Type} : Operand.State A → Bool
  | .done _ => true
  | _ => false

private def scan {A : Type} [Fintype A] (m : Move) (step : A → Bool → Bool × A) (a : A) :=
  FiniteRoutine.ofStackCode (Operand.code step) (ports m) (.clear a) normal

private theorem scan_runs {A : Type} [Fintype A] (m : Move) (step : A → Bool → Bool × A)
    (a final : A) (s : Stacks Port) (z : List Bool) {t : ℕ}
    (ht : s (.buffer .temp) = []) (ho : s (.buffer .output) = [])
    (h : StackRuns (Operand.code step) t (.clear a) (scanStacks (s m.src) [] [] (s m.dst))
      (.done final) (scanStacks (s m.src) [] [] z)) :
    (scan m step a).Runs t s (Function.update s m.dst z) := by
  apply FiniteRoutine.runs_ofStackCode_framed (ports_inj m) (normal := normal) rfl
    (exit := .done final) rfl (fun q hn => by cases q <;> first | rfl | contradiction) h
  · intro i; cases i <;> first | rfl | exact ht | exact ho
  · intro i
    cases m <;> cases i <;> simp [ports, Move.dst, Move.src, scanStacks, ht, ho]
  · intro k hk; exact Function.update_of_ne (Ne.symm (hk .out)) ..

private def delay (prev b : Bool) := (prev, b)
private def inc (carry b : Bool) := (b ^^ carry, b && carry)

private theorem delay_spec (p : Bool) (xs : List Bool) :
    (Operand.emitted delay p xs).1.length = xs.length ∧
    value (Operand.emitted delay p xs).1 + 2^xs.length * (Operand.emitted delay p xs).2.toNat =
      p.toNat + 2*value xs := by
  induction xs generalizing p with
  | nil => simp [Operand.emitted, value]
  | cons b xs ih =>
    obtain ⟨hl, hv⟩ := ih b
    simp only [Operand.emitted, delay, List.length_cons, hl, value, pow_succ]
    constructor
    · trivial
    · rw [show 2^xs.length*2*(Operand.emitted delay b xs).2.toNat =
          2*(2^xs.length*(Operand.emitted delay b xs).2.toNat) by ring]
      omega

private theorem inc_emitted (p : Bool) (xs : List Bool) :
    Operand.emitted inc p xs = UnaryWord.incScan p xs := by
  induction xs generalizing p with
  | nil => rfl
  | cons b xs ih => simp [Operand.emitted, UnaryWord.incScan, inc, ih]

/-- Fixed named-stack word table. Its number of control states depends only on the operation. -/
def load (m : Move) : Op → FiniteRoutine Port
  | .copy => scan m Operand.copyBit ()
  | .literal n => scan m (Operand.literalBit n) (Fin.last n)
  | .double p => scan m delay p
  | .increment => scan m inc true

/-- The word scanner performs one pass in each direction and clears the old destination. -/
theorem load_runs {w : ℕ} (m : Move) (op : Op) (s : Stacks Port) (a : Word w)
    (hs : s m.src = wordBits a) (ht : s (.buffer .temp) = []) (ho : s (.buffer .output) = []) :
    (load m op).Runs ((s m.dst).length + 7*w+3) s
      (Function.update s m.dst (wordBits (Fin.ofNat (2^w) (op.eval a.val)))) := by
  let xs := wordBits a
  have len : xs.length = w := length_wordBits _
  cases op with
  | copy =>
    have ha : Fin.ofNat (2^w) a.val = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
    rw [Op.eval, ha]
    apply scan_runs m _ _ () _ _ ht ho
    simpa only [hs, length_wordBits] using Operand.copy_run (wordBits a) (s m.dst)
  | literal n =>
    obtain ⟨z, hr⟩ := Operand.literal_run n a (s m.dst)
    apply scan_runs m _ _ z _ _ ht ho
    simpa only [hs, Op.eval] using hr
  | double p =>
    obtain ⟨hl, hv⟩ := delay_spec p xs
    let z := Operand.emitted delay p xs
    have hlo := value_lt z.1
    rw [show z.1.length = w from hl.trans len] at hlo
    have he : z.1 = wordBits (Fin.ofNat (2^w) (2*a.val+p.toNat)) := by
      apply eq_of_length_value (by simp only [length_wordBits]; exact hl.trans len)
      rw [value_wordBits, Fin.val_ofNat, Nat.add_comm]
      rw [← Nat.mod_eq_of_lt hlo]
      have hmod := congrArg (· % (2^w)) hv
      simpa only [len, Nat.add_mul_mod_self_left, xs, value_wordBits] using hmod
    apply scan_runs m _ _ z.2 _ _ ht ho
    simpa only [hs, xs, length_wordBits, Op.eval, ← he] using Operand.run delay p xs (s m.dst)
  | increment =>
    let z := UnaryWord.incScan true xs
    have hl : z.1.length = w := (UnaryWord.incScan_length ..).trans len
    have hlo := value_lt z.1
    rw [hl] at hlo
    have he : z.1 = wordBits (Fin.ofNat (2^w) (a.val+1)) := by
      apply eq_of_length_value (by simp only [length_wordBits]; exact hl)
      rw [← Nat.mod_eq_of_lt hlo]
      have hmod := congrArg (· % (2^w)) (UnaryWord.incScan_value true xs)
      simpa only [len, Nat.add_mul_mod_self_left, xs, value_wordBits,
        Bool.toNat_true, Fin.val_ofNat] using hmod
    apply scan_runs m _ _ z.2 _ _ ht ho
    simpa only [hs, inc_emitted, xs, length_wordBits, Op.eval, ← he] using Operand.run inc true xs (s m.dst)

end TeamTapeInputEmit

end BorderVNP
end Computability
end OAI
