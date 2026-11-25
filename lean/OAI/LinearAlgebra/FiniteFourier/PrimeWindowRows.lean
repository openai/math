import OAI.LinearAlgebra.FiniteFourier.PrimeWindow

/-! # Exceptional rows for repeated copies of each shift

A repair row is indexed by its shift and a repetition number. All copies of
one shift have the same shifted count at a given frequency.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

variable {ℓ m : ℕ} [NeZero ℓ]

/-- Exceptional rows among `B` copies of every shift. -/
def exceptionalShiftRows (k : Fin m → ZMod ℓ) (B : ℕ) :
    Finset ((Fin m → ZMod ℓ) × Fin B) :=
  exceptionalShifts k ×ˢ Finset.univ

@[simp] theorem mem_exceptionalShiftRows (k : Fin m → ZMod ℓ) {B : ℕ}
    (r : (Fin m → ZMod ℓ) × Fin B) :
    r ∈ exceptionalShiftRows k B ↔
      (shiftedCount k r.1 : ℤ) ∉ Set.Icc (repairWindowLower ℓ m) (repairWindowUpper ℓ m) := by
  simp [exceptionalShiftRows, exceptionalShifts]

/-- Repetition preserves the bound on the exceptional fraction. -/
theorem exceptionalShiftRows_card_le (hℓ : 2 ≤ ℓ) (hm : 2 ≤ m)
    (k : Fin m → ZMod ℓ) (B : ℕ) :
    (exceptionalShiftRows k B).card ≤ (ℓ ^ m * B) / (2 * m ^ 3) := by
  have hpos : 0 < 2 * m ^ 3 := by positivity
  have h := (Nat.le_div_iff_mul_le hpos).mp (exceptionalShifts_card_le hℓ hm k)
  apply (Nat.le_div_iff_mul_le hpos).mpr
  simpa [exceptionalShiftRows, Nat.mul_right_comm] using Nat.mul_le_mul_right B h

/-- Number the shift-repetition pairs by consecutive indices. -/
def shiftRowEquivFin (ℓ m B : ℕ) [NeZero ℓ] :
    ((Fin m → ZMod ℓ) × Fin B) ≃ Fin (ℓ ^ m * B) :=
  Fintype.equivFinOfCardEq (by simp [ZMod.card])

/-- The exceptional set in the consecutive numbering of the repair rows. -/
def exceptionalShiftRowIndices (k : Fin m → ZMod ℓ) (B : ℕ) : Finset (Fin (ℓ ^ m * B)) :=
  (exceptionalShiftRows k B).map (shiftRowEquivFin ℓ m B).toEmbedding

@[simp] theorem mem_exceptionalShiftRowIndices (k : Fin m → ZMod ℓ) {B : ℕ}
    (i : Fin (ℓ ^ m * B)) :
    i ∈ exceptionalShiftRowIndices k B ↔
      (shiftedCount k ((shiftRowEquivFin ℓ m B).symm i).1 : ℤ) ∉
        Set.Icc (repairWindowLower ℓ m) (repairWindowUpper ℓ m) := by
  rw [exceptionalShiftRowIndices, Finset.mem_map_equiv, mem_exceptionalShiftRows]

theorem exceptionalShiftRowIndices_card_le (hℓ : 2 ≤ ℓ) (hm : 2 ≤ m)
    (k : Fin m → ZMod ℓ) (B : ℕ) :
    (exceptionalShiftRowIndices k B).card ≤ (ℓ ^ m * B) / (2 * m ^ 3) := by
  simpa [exceptionalShiftRowIndices] using exceptionalShiftRows_card_le hℓ hm k B

end

end

end FiniteFourier
end LinearAlgebra
end OAI
