import OAI.Optimization.LinearProgramming.PrimalDual.Bits

/-! Uniform encoding bounds for rectangular rational matrix multiplication. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix
open scoped BigOperators Matrix

/-- A common bit bound for every partial dot product of length at most k
from two sets of rational inputs bounded by a and b bits. -/
def dotBitBound (k a b : ℕ) : ℕ := 3 + 2 * k * (a + b + 1)

theorem dotProduct_partial_bits {k a b : ℕ} (x y : Fin k → ℚ)
    (hx : ∀ i, RAM.ratBits (x i) ≤ a) (hy : ∀ i, RAM.ratBits (y i) ≤ b)
    (s : Finset (Fin k)) :
    RAM.ratBits (∑ i ∈ s, x i * y i) ≤ dotBitBound k a b := by
  apply (PrimalDual.ratBits_partial_dot_le s x y).trans
  have hsum : (∑ i ∈ s, (RAM.ratBits (x i) + RAM.ratBits (y i) + 1)) ≤
      k * (a + b + 1) := by
    calc
      _ ≤ ∑ _ ∈ s, (a + b + 1) := Finset.sum_le_sum fun i _ => Nat.add_le_add_right (Nat.add_le_add (hx i) (hy i)) 1
      _ = s.card * (a + b + 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by simpa using s.card_le_univ)
  unfold dotBitBound
  simpa only [Nat.mul_assoc] using Nat.add_le_add_left (Nat.mul_le_mul_left 2 hsum) 3

/-- Encoding bound for each entry of the materialized matrix product. -/
theorem matrix_product_bits {m k n a b : ℕ} (A : Matrix (Fin m) (Fin k) ℚ)
    (B : Matrix (Fin k) (Fin n) ℚ) (hA : ∀ i j, RAM.ratBits (A i j) ≤ a)
    (hB : ∀ i j, RAM.ratBits (B i j) ≤ b) (i : Fin m) (j : Fin n) :
    RAM.ratBits ((A * B) i j) ≤ dotBitBound k a b := by
  exact dotProduct_partial_bits (A i) (B.col j) (hA i) (fun t => hB t j) Finset.univ

end Geometry
end LinearProgramming
end Optimization
end OAI
