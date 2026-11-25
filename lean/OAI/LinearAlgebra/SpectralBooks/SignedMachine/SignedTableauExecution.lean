import OAI.LinearAlgebra.SpectralBooks.MachinePadding
import Mathlib.Tactic

/-! # Local execution rules for the clocked signed computation tableau

One bit is available at every clock tick. Forced ticks require a zero bit.
Padding a halted computation by zero bits gives exactly one assignment per
halting path, including when both successors of a branch coincide. Tape cells
are addressed relative to their current head, so a step reads three adjacent
columns of the preceding tape row.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedMachine

/-- The offset of the new head from the old one. -/
def Direction.offset : Direction → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

/-- The symbol at any relative position, including unvisited blank cells. -/
def Tape.atCell (t : Tape) : ℤ → Symbol
  | .ofNat 0 => t.head
  | .ofNat (n+1) => t.right.getD n .blank
  | .negSucc n => t.left.getD n .blank

@[simp] theorem Tape.atCell_zero (t : Tape) : t.atCell 0 = t.head := rfl

private def shiftCell : Direction → ℤ → ℤ
  | .stay, i => i
  | .left, .ofNat 0 => .negSucc 0
  | .left, .ofNat (n+1) => .ofNat n
  | .left, .negSucc n => .negSucc (n+1)
  | .right, .ofNat n => .ofNat (n+1)
  | .right, .negSucc 0 => .ofNat 0
  | .right, .negSucc (n+1) => .negSucc n

private theorem shiftCell_eq (d : Direction) (i : ℤ) : shiftCell d i = i + d.offset := by
  cases d <;> cases i with
  | ofNat n => cases n <;> simp [shiftCell, Direction.offset]
  | negSucc n => cases n <;> simp [shiftCell, Direction.offset] <;> omega

/-- Every new cell is copied from the cell offset by the head move. -/
theorem Tape.atCell_move (t : Tape) (d : Direction) (i : ℤ) :
    (t.move d).atCell i = t.atCell (i + d.offset) := by
  rw [← shiftCell_eq]
  obtain ⟨l, h, r⟩ := t
  cases d <;> cases i with
  | ofNat n =>
    cases n with
    | zero => cases l <;> cases r <;> rfl
    | succ n => cases n <;> cases l <;> cases r <;> simp only [shiftCell, Tape.move, Tape.atCell] <;> simp
  | negSucc n => cases n <;> cases l <;> cases r <;> simp only [shiftCell, Tape.move, Tape.atCell] <;> simp

/-- A work tape performs the indicated write at the old head only. -/
theorem Tape.atCell_writeMove (t : Tape) (s : Symbol) (d : Direction) (i : ℤ) :
    (t.writeMove (s,d)).atCell i =
      if i + d.offset = 0 then s else t.atCell (i + d.offset) := by
  rw [Tape.writeMove, Tape.atCell_move]
  generalize i + d.offset = j
  cases j with
  | ofNat k => cases k <;> rfl
  | negSucc k => rfl

/-- A deterministic tick of the tableau, given the bit chosen for this time. -/
def tableauStep {C : Type*} (next : C → Outcome C) (bit : Bool) : Output ⊕ C → Output ⊕ C
  | .inl out => .inl (if bit then .zero else out)
  | .inr c =>
    match next c with
    | .fail => .inl .zero
    | .halt out => .inl (if bit then .zero else out)
    | .step y => if bit then .inl .zero else .inr y
    | .branch a b => .inr (if bit then b else a)

/-- Read the bits of a fixed-length tableau in chronological order. -/
def tableauOutput {C : Type*} (next : C → Outcome C) :
    (fuel : ℕ) → (Fin fuel → Bool) → Output ⊕ C → Output
  | 0, _, c => c.elim id fun _ => .zero
  | n+1, bits, c => tableauOutput next n (Fin.tail bits) (tableauStep next (bits 0) c)

/-- Summing the unique padded presentations of all runs gives the original
clocked signed path sum on a live configuration, and the sign on a halted one. -/
theorem sum_tableauOutput {C : Type*} (next : C → Outcome C) (fuel : ℕ) (c : Output ⊕ C) :
    ∑ bits : Fin fuel → Bool, (tableauOutput next fuel bits c).value =
      c.elim Output.value (run next fuel) := by
  induction fuel generalizing c with
  | zero =>
    cases c <;> simp [tableauOutput, run, Output.value]
  | succ n ih =>
    let e := Fin.consEquiv fun _ : Fin (n+1) => Bool
    rw [← e.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
    change (∑ tail : Fin n → Bool, (tableauOutput next n tail (tableauStep next true c)).value) +
      (∑ tail : Fin n → Bool, (tableauOutput next n tail (tableauStep next false c)).value) = _
    rw [ih, ih]
    rcases c with o | c
    · simp [tableauStep, Output.value]
    · cases h : next c <;> simp [tableauStep, run, h, Output.value, add_comm]

end SignedMachine

end SpectralBooks
end LinearAlgebra
end OAI
