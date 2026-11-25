import Mathlib.Computability.TuringMachine.ToPartrec

/-! # Reading the little-endian numerals emitted by the Mathlib TM2 generator -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorROM
open Turing.PartrecToTM2

def digitsValue : List Γ' → ℕ
  | [] => 0
  | g :: more => (if g = .bit1 then 1 else 0) + 2 * digitsValue more

private theorem digitsValue_pos (p : PosNum) : digitsValue (trPosNum p) = (p:ℕ) := by
  induction p with
  | one => rfl
  | bit0 p ih => simp [trPosNum, digitsValue, ih, PosNum.cast_bit0]; omega
  | bit1 p ih => simp [trPosNum, digitsValue, ih, PosNum.cast_bit1]; omega

theorem digitsValue_nat (n : ℕ) : digitsValue (trNat n) = n := by
  have aux (u : Num) : digitsValue (trNum u) = (u:ℕ) := by
    cases u with
    | zero => rfl
    | pos p => exact digitsValue_pos p
  simpa [trNat] using aux (n:Num)

theorem digits_only (n : ℕ) : ∀ g ∈ trNat n, g = Γ'.bit0 ∨ g = .bit1 := by
  have pos (p : PosNum) : ∀ g ∈ trPosNum p, g = Γ'.bit0 ∨ g = .bit1 := by
    induction p with
    | one => simp [trPosNum]
    | bit0 p ih => simpa [trPosNum] using ih
    | bit1 p ih => simpa [trPosNum] using ih
  unfold trNat
  cases (n:Num) with
  | zero => simp [trNum]
  | pos p => exact pos p

end GeneratorROM

end NearSquareRoot
end Computability
end OAI
