import OAI.Computability.IntegerMultiplication.Code.Fold
import Mathlib.Tactic.Linarith

/-! # Encoded volumes of Cartesian-product rows

Replicating the right input and then storing all pairs costs one copy of
each encoded entry for every choice in the other input.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Cartesian

open IntegerMultiplication.Code

variable {X Y : Type*} [Codec X] [Codec Y]

/-- Encoded size of all pairs in a row with fixed first entry. -/
theorem size_pair_row (x : X) (r : List Y) :
    size (r.map fun y => (x, y)) = size r + r.length * (size x + 1) := by
  induction r with
  | nil => simp
  | cons y r ih => simp [ih, Nat.add_mul]; omega

/-- The intermediate rows, their individual processing budgets, and the list
of output rows fit within three times the Cartesian traversal budget. -/
theorem cartesian_row_budget (l : List X) (r : List Y) :
    size (l.map fun x => (x, r)) +
      costSum (fun z : X × List Y => (z.2.length + 1) * size z.1 + size z.2)
        (l.map fun x => (x, r)) +
      size (l.map fun x => r.map fun y => (x, y)) ≤
      3 * (size l * (r.length + 1) + size r * (l.length + 1) + 1) := by
  induction l with
  | nil => simp; omega
  | cons x l ih =>
    simp only [List.map_cons, costSum_cons, size_cons, size_prod, size_pair_row,
      List.length_cons]
    nlinarith

end Cartesian

end NearSquareRoot
end Computability
end OAI
