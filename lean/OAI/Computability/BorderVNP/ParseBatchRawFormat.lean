import OAI.Computability.BorderVNP.ParseBatchRawWord
import OAI.Computability.BorderVNP.ParseBatchFormatCircuit
import OAI.Computability.BorderVNP.ParseBatchExprSubstitution

/-! # Field checks on the physical parse-record input pins -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP.VerifierNetwork BorderVNP.ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin

private def operand (m g n w v : ℕ) : FormatWord → Fin w → Expr (BitSlot v)
  | .parent => rawWord w 0
  | .layer => rawWord w 1
  | .split => rawWord w 2
  | .left => rawWord w 3
  | .right => rawWord w 4
  | .position => rawWord w 5
  | .variables => constWord w m
  | .states => constWord w g
  | .layers => constWord w n
  | .zero => constWord w 0

private def pins (m g n : ℕ) :
    FormatPin (recordWidth m g n + 3) → Expr (BitSlot (recordWidth m g n))
  | .inl t => .input (.inl t)
  | .inr (f,i) => operand m g n _ _ f i

/-- Evaluate the range and padding tests on the actual guessed record, supplying the
bounds as constants and converting its six numerical fields to the working bit order. -/
def rawFormat (m g n : ℕ) : Expr (BitSlot (recordWidth m g n)) :=
  plugExpr (pins m g n) (formatExpr (recordWidth m g n+3))

/-- Acceptance of the physical expression is precisely successful canonical decoding. -/
theorem rawFormat_eval (m g n : ℕ) (z : BitSlot (recordWidth m g n) → Bool) :
    (rawFormat m g n).eval z = true ↔ ∃ t, unpack m g n (fieldsOfBits z) = some t := by
  let w := recordWidth m g n + 3
  let y (i : FormatPin w) := (pins m g n i).eval z
  have hmax : max m (max g n) < 2^w := by
    have h : max m (max g n) + 1 ≤ 2^recordWidth m g n := Nat.le_pow_clog (by decide) _
    exact (Nat.lt_of_succ_le h).trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [w]; omega))
  have hf (f : FormatWord) : formatWord y f = wordValue z (operand m g n w _ f) := rfl
  have hz : formatWord y .zero = 0 := (hf _).trans (constWord_value z w 0 (by positivity))
  have hm : formatWord y .variables = m := (hf _).trans (constWord_value z w m (by omega))
  have hg : formatWord y .states = g := (hf _).trans (constWord_value z w g (by omega))
  have hn : formatWord y .layers = n := (hf _).trans (constWord_value z w n (by omega))
  have hw : recordWidth m g n ≤ w := by dsimp [w]; omega
  have hfields : fieldsFromPins y = fieldsOfBits z := by
    simp only [fieldsFromPins, hf, operand, rawWord_value hw, Fields.word]
    rfl
  rw [rawFormat, plugExpr_eval]
  exact (formatExpr_eval y hz).trans (by rw [hm, hg, hn, hfields])

/-- Physical bit selection and fixed bounds retain the original linear size estimate. -/
theorem rawFormat_size (m g n : ℕ) : (rawFormat m g n).size ≤ 165*(recordWidth m g n+3)+40 := by
  have hs (i : FormatPin (recordWidth m g n+3)) : (pins m g n i).size ≤ 1 := by
    rcases i with t | ⟨f,i⟩
    · exact le_rfl
    · cases f <;> simp [pins, operand, rawWord_size, constWord_size]
  exact (plugExpr_size _ _ le_rfl hs).trans (by simpa only [Nat.mul_one] using formatExpr_size _)

end ParseRecords

end BorderVNP
end Computability
end OAI
