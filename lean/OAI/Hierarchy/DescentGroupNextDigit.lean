import Mathlib.Data.Nat.Basic

namespace OAI
/-! Bounded low digits give the lexicographic order of packed natural numbers. -/
namespace Hierarchy.DescentSixParty.GroupStage

theorem nextDigit {a b x y p : ℕ} (hx : x<p) (hy : y<p) :
    a*p+x<b*p+y ↔ a<b ∨ a=b ∧ x<y := by
  rcases lt_trichotomy a b with lt|eqn|gt
  · have hi := Nat.mul_le_mul_right p lt
    rw [Nat.succ_mul] at hi
    omega
  · subst b
    omega
  · have hi := Nat.mul_le_mul_right p gt
    rw [Nat.succ_mul] at hi
    omega

end Hierarchy.DescentSixParty.GroupStage

end OAI
