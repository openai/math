import OAI.Hierarchy.Models

namespace OAI
/-! # Depth and gate count of binary arithmetic formulas -/

namespace Hierarchy.Formula

open MatrixMultiplication.Arithmetic

variable {F : Type*} {σ : Type}

/-- The number of binary gates on the longest root-to-leaf path. -/
def depth : Formula F σ → ℕ
  | .constant _ | .input _ => 0
  | .add a b | .sub a b | .mul a b => max (depth a) (depth b) + 1

theorem depth_le_cost (f : Formula F σ) : depth f ≤ f.cost := by
  induction f <;> simp only [depth, Expression.cost] at * <;> omega

private theorem node_le_pow (a b : Formula F σ)
    (ha : a.cost + 1 ≤ 2 ^ depth a) (hb : b.cost + 1 ≤ 2 ^ depth b) :
    a.cost + b.cost + 1 + 1 ≤ 2 ^ (max (depth a) (depth b) + 1) := by
  have left := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_left (depth a) (depth b))
  have right := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_right (depth a) (depth b))
  rw [pow_succ]
  omega

/-- A binary formula of depth `d` has at most `2^d` leaves. -/
theorem cost_succ_le_pow_depth (f : Formula F σ) : f.cost + 1 ≤ 2 ^ depth f := by
  induction f with
  | constant _ | input _ => exact Nat.le_refl 1
  | add a b ha hb | sub a b ha hb | mul a b ha hb => exact node_le_pow a b ha hb

end Hierarchy.Formula

end OAI
