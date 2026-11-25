import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramSlotCircuit
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramDistinctCircuit
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramOneHot
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramZeroPadding

/-! # Parser circuit for the signed universal machine

The raw guess includes the padded table, body length, and a one-hot cursor
row for each field boundary. The parser circuit reads all of them and checks
the program prefix while leaving the arbitrary payload suffix available.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SignedProgram.Hot

open ExactQuantumFactoring BooleanNetwork

variable {n a : ℕ}

/-- A disabled table coordinate must contain the zero code. -/
def paddingNet (read : CellReader n a) : BooleanNetwork a 1 :=
  Unary.andOver fun c : Cell n => (activeNet read c).bor (read c 0)

theorem paddingNet_correct {read : CellReader n a} {x : Basis a} {t : Table n}
    (h : read.Agrees x t) : (paddingNet read).eval x 0 = true ↔ t.Canonical := by
  rw [paddingNet, Unary.andOver_eval, ← zeroPadding_iff]
  apply forall_congr'
  intro c
  rw [eval_bor, activeNet_correct h, h]
  cases ha : c.active t <;> simp

def paddingBudget (n C : ℕ) := (2+n*(8+5*n))*(activeBudget n C+C+5)+1

theorem paddingNet_count {read : CellReader n a} {C : ℕ} (h : read.Bounded C) :
    (paddingNet read).net.count ≤ paddingBudget n C := by
  apply (Unary.andOver_count _ (C := activeBudget n C+C+4) ?_).trans
  · unfold paddingBudget
    gcongr
    exact cells_card_le n
  · intro c
    simp only [count_bor]
    have := activeNet_count h c
    have := h c 0
    omega

/-- Connect the input bits, one-hot fields and cursor guesses to the unary scanner. -/
def wires (n : ℕ) : Unary.Wires (n+decodeGuessWidth n) n (slotsCount n) where
  input i := bit (i.castAdd _)
  field := slotNet (fieldBit n) (frameWire n)
  cursor := cursorWire n

/-- All syntax, padding, and duplicate-key tests for the signed program prefix. -/
def parseNet (n : ℕ) : BooleanNetwork (n+decodeGuessWidth n) 1 :=
  (codeNet n).band <| (frameCodeNet n).band <| (paddingNet (fieldBit n)).band <|
    (distinctRows (fieldBit n)).band <| (fitsNet (fieldBit n)).band <|
    (Unary.check (wires n)).band (Unary.frameTest (frameWire n) (cursorWire n (Fin.last (slotsCount n))))

private theorem readBound (n : ℕ) : CellReader.Bounded (fieldBit n) 1 := fieldBit_count n

/-- Gate complexity of the concrete decoder as a function only of the input length. -/
theorem parseNet_count (n : ℕ) : (parseNet n).net.count ≤ 1000000*(n+2)^6 := by
  have hc := codeNet_count n
  have hf := frameCodeNet_count n
  have hp := paddingNet_count (readBound n)
  have hd := distinctRows_count (readBound n)
  have hfit := fitsNet_count (readBound n)
  have hcurs := Unary.check_count (wires n) (slotBudget n 1)
    (fun _ => Nat.zero_le _)
    (slotNet_count (readBound n) (frameWire n) (fun _ => Nat.zero_le 1))
    (fun _ _ => Nat.zero_le _)
  have hlast := Unary.frameTest_count (frameWire n) (cursorWire n (Fin.last (slotsCount n))) (C := 0)
    (fun _ => le_rfl) (fun _ => le_rfl)
  rw [parseNet]
  simp only [count_band]
  calc
    _ ≤ ((2+n*(8+5*n))*((n+3)*((n+3)*2+5)+2)+1) +
        (((n+1)*((n+1)*2+5)+1) + (paddingBudget n 1 + (distinctRowsBound n 1 +
          (fitsBudget n 1 + (200*(slotsCount n+1)*(n+2)^3*(slotBudget n 1+1) + ((n+1)*(2*0+5)+1) + 1)
          + 1) + 1) + 1) + 1) + 1 := by omega
    _ ≤ _ := by
      dsimp only [paddingBudget, distinctRowsBound, rowMatchBudget, fitsBudget, activeBudget,
        slotBudget, slotsCount]
      zify
      rw [← sub_nonneg]
      ring_nf
      positivity

end SignedProgram.Hot

end

end SpectralBooks
end LinearAlgebra
end OAI
