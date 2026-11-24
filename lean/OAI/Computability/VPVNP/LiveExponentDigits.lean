import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Checking a running exponent one bit at a time

In the first half of the live chain an increment fits in one RAM word, while
the incoming and outgoing exponents may occupy many words. A digit call
checks the low bit of the sum and passes its quotient by two to the next
digit. Requiring zero final carry checks ordinary natural-number addition.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveExponent

open BurstRAM
open PrimedCounter.GuessWord (value)

private theorem boolDigit (b : Bool) : (finTwoEquiv.symm b).val = b.toNat := by
  cases b <;> rfl

/-- The carry and the low input bit of one digit. -/
def total (c : ℕ) (b : Bool) := c + b.toNat

/-- Each digit must match the outgoing bit. The final digit's carry must vanish. -/
def Checks : ℕ → List Bool → List Bool → Prop
  | c, [], [] => c = 0
  | c, x :: xs, y :: ys => y.toNat = total c x % 2 ∧ Checks (total c x / 2) xs ys
  | _, _, _ => False

/-- The checks enforce the full-width equation including overflow. -/
theorem checks_iff {c : ℕ} {xs ys : List Bool} (hlen : xs.length = ys.length) :
    Checks c xs ys ↔ value ys = value xs + c := by
  induction xs generalizing c ys with
  | nil =>
    cases ys <;> simp_all [Checks, value, eq_comm]
  | cons b xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons d ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [Checks, ih hlen]
      simp only [value, boolDigit, total]
      have hd : d.toNat ≤ 1 := by cases d <;> decide
      omega

/-- Specialization to the actual little-endian cut encoding. -/
theorem checks_words {Z : ℕ} (c : ℕ) (x y : Word Z) :
    Checks c (wordBits x) (wordBits y) ↔ y.val = x.val + c := by
  rw [checks_iff (by simp), PrimedCounter.GuessWord.value_wordBits,
    PrimedCounter.GuessWord.value_wordBits]

/-- Even with a long binary input exponent, the carry never grows above the
larger of the initial increment and one. -/
theorem carry_le {B c : ℕ} (hc : c ≤ B) (b : Bool) : total c b / 2 ≤ B := by
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  unfold total
  omega

end LiveExponent

end VPVNP
end Computability
end OAI
