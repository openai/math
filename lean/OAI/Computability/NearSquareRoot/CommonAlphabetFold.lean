import OAI.Computability.IntegerMultiplication.TMModel
import Mathlib.Tactic

/-! # A single tape measures the unsigned distance of an arbitrary physical head -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Align
open IntegerMultiplication TM

def flip : Move → Move | .left => .right | .right => .left | .stay => .stay

def foldMove (atOrigin neg : Bool) (d : Move) : Move :=
  if atOrigin then match d with | .stay => .stay | _ => .right
  else if neg then flip d else d

def foldSign (atOrigin neg : Bool) (d : Move) :=
  if atOrigin then match d with | .left => true | _ => false else neg

def toward (neg : Bool) : Move := if neg then .right else .left

/-- The old sign is relevant only away from the origin sentinel. -/
theorem folded (p : ℤ) (neg : Bool) (known : p ≠ 0 → neg = decide (p<0)) (d : Move) :
    (p.natAbs : ℤ)+(foldMove (decide (p=0)) neg d).shift = ((p+d.shift).natAbs : ℤ) ∧
      (p+d.shift ≠ 0 → foldSign (decide (p=0)) neg d = decide (p+d.shift<0)) := by
  by_cases hz : p = 0
  · subst p
    cases d <;> decide +revert
  rw [known hz]
  constructor
  · by_cases hn : p < 0
    · cases d <;> simp [foldMove,Move.shift,flip,hz,hn,
        abs_of_nonpos (by omega : p ≤ 0), abs_of_nonpos (by omega : p + -1 ≤ 0),
        abs_of_nonpos (by omega : p+1 ≤ 0)] <;> omega
    · cases d <;> simp [foldMove,Move.shift,hz,hn,
        abs_of_nonneg (by omega : 0 ≤ p), abs_of_nonneg (by omega : 0 ≤ p + -1),
        abs_of_nonneg (by omega : 0 ≤ p+1)]
  · intro h
    simp only [foldSign, decide_eq_false hz, Bool.false_eq_true, ite_false]
    apply Bool.decide_congr
    cases d <;> simp [Move.shift] at * <;> omega

/-- Location on the chosen side of the origin at unsigned distance `n`. -/
def side (neg : Bool) (n : ℕ) : ℤ := if neg then -(n:ℤ) else n

theorem side_natAbs (p : ℤ) (neg : Bool) (h : p ≠ 0 → neg = decide (p<0)) :
    side neg p.natAbs = p := by
  by_cases hp : p=0
  · subst p; cases neg <;> rfl
  · rw [h hp]
    cases p <;> simp [side]
    omega

@[simp] theorem side_step (neg : Bool) (n : ℕ) :
    side neg (n+1)+(toward neg).shift = side neg n := by
  cases neg <;> simp [side,toward,Move.shift]

end CommonAlphabet.Align

end NearSquareRoot
end Computability
end OAI
