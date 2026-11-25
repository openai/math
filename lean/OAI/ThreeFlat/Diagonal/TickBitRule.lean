import Mathlib.Data.Nat.Notation

namespace OAI
/-! # Bitwise relations between two physical endpoints -/

namespace ThreeFlat.Diagonal.TickAuxiliary

inductive Rule
  | any | same | oldZero | newZero | bothZero | zeroOne | oneZero | bothOne
  deriving DecidableEq, Repr

def Rule.holds : Rule → Bool → Bool → Prop
  | .any, _, _ => True
  | .same, a, b => a = b
  | .oldZero, a, _ => a = false
  | .newZero, _, b => b = false
  | .bothZero, a, b => a = false ∧ b = false
  | .zeroOne, a, b => a = false ∧ b = true
  | .oneZero, a, b => a = true ∧ b = false
  | .bothOne, a, b => a = true ∧ b = true

def Rule.tag : Rule → ℕ
  | .any => 0 | .same => 1 | .oldZero => 2 | .newZero => 3
  | .bothZero => 4 | .zeroOne => 5 | .oneZero => 6 | .bothOne => 7

end ThreeFlat.Diagonal.TickAuxiliary

end OAI
