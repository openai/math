import OAI.ThreeFlat.Diagonal.LaneCursor
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Contiguous trace buckets and XOR partners

A row has a binary high-bit lane and a low ordinal inside its bucket.
XOR by a public row offset translates the lane by its high part and
translates the ordinal by its low part.
-/

namespace ThreeFlat.Diagonal.LaneCursor

abbrev Row (k low : ℕ) := Fin (2 ^ k * 2 ^ low)

/-- Enumerate all trace rows by lane and within-bucket location. -/
def splitRow (k low : ℕ) : Row k low ≃ Lane k × Fin (2 ^ low) :=
  finProdFinEquiv.symm.trans (finFunctionFinEquiv.symm.prodCongr (Equiv.refl _))

theorem splitRow_lane {k low : ℕ} (row : Row k low) :
    (splitRow k low row).1 = highBits k low row.val := by
  funext i
  apply Fin.ext
  change row.val / 2 ^ low / 2 ^ i.val % 2 = (if (row.val >>> low).testBit i.val then
      (1 : Fin 2) else 0).val
  rw [Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  by_cases one : row.val / 2 ^ low / 2 ^ i.val % 2 = 1
  · simp [one]
  · have zero : row.val / 2 ^ low / 2 ^ i.val % 2 = 0 := by omega
    simp [zero]

@[simp] theorem splitRow_low {k low : ℕ} (row : Row k low) :
    (splitRow k low row).2.val = row.val % 2 ^ low := rfl

/-- The row indexed by a public XOR partner mask. -/
def partner {k low : ℕ} (row offset : Row k low) : Row k low :=
  ⟨row.val ^^^ offset.val, by
    have hr : row.val < 2 ^ (k + low) := row.isLt.trans_eq (Nat.pow_add 2 k low).symm
    have hm : offset.val < 2 ^ (k + low) := offset.isLt.trans_eq (Nat.pow_add 2 k low).symm
    exact (Nat.xor_lt_two_pow hr hm).trans_eq (Nat.pow_add 2 k low)⟩

theorem partner_coordinates {k low : ℕ} (row offset : Row k low) :
    (splitRow k low (partner row offset)).1 =
        (splitRow k low row).1 + (splitRow k low offset).1 ∧
      (splitRow k low (partner row offset)).2.val =
        (splitRow k low row).2.val ^^^ (splitRow k low offset).2.val := by
  constructor
  · simp only [splitRow_lane, partner, highBits_xor]
  · exact Nat.xor_mod_two_pow

/-- The actual lane path ends at the physical bucket of the partner row. -/
theorem row_route_endpoint {k low : ℕ} (row offset : Row k low) :
    stage ((splitRow k low offset).1) k ((splitRow k low row).1) =
      (splitRow k low (partner row offset)).1 := by
  rw [stage_end, (partner_coordinates row offset).1]

end ThreeFlat.Diagonal.LaneCursor

end OAI
