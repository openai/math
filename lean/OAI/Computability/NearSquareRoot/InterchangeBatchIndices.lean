import Mathlib.Algebra.Order.Floor.Div

/-!
# Splitting a radix digit into a batch index and an independent row

Arrange a radix-`b` digit in groups of `W` consecutive values. Complete the last
partial group by repeating digit values cyclically from zero. After independent
row processing, the quotient and remainder select each genuine digit uniquely.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BatchRows

/-- Number of groups in a (possibly padded) row. -/
def groups (b W : ℕ) : ℕ := b ⌈/⌉ W

variable {b W : ℕ}

theorem le_groups_volume (hW : 0 < W) : b ≤ W * groups b W :=
  (ceilDiv_le_iff_le_mul hW).mp le_rfl

/-- Each padded group has `W` positions; at most `W-1` positions are padding. -/
theorem groups_volume_lt (hW : 0 < W) : W * groups b W < b + W := by
  rw [groups, Nat.ceilDiv_eq_add_pred_div, Nat.mul_comm]
  have := Nat.div_mul_le_self (b + W - 1) W
  omega

theorem groups_volume_le_twice (hW : 0 < W) (hWb : W ≤ b) :
    W * groups b W ≤ 2 * b := by
  have := groups_volume_lt (b := b) hW
  omega

/-- The genuine digit represented by the row and group. Values beyond the
last digit are copies of initial values in the alphabet. -/
def select (hb : 0 < b) (u : Fin W) (g : Fin (groups b W)) : Fin b :=
  ⟨(g.val * W + u.val) % b, Nat.mod_lt _ hb⟩

def row (hW : 0 < W) (i : Fin b) : Fin W := ⟨i.val % W, Nat.mod_lt _ hW⟩

def group (hW : 0 < W) (i : Fin b) : Fin (groups b W) :=
  ⟨i.val / W, (Nat.div_lt_iff_lt_mul hW).mpr
    (i.isLt.trans_le (Nat.mul_comm _ _ ▸ le_groups_volume hW))⟩

theorem group_mul_add_row (hW : 0 < W) (i : Fin b) :
    (group hW i).val * W + (row hW i).val = i.val := by
  simpa only [group, row, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div i.val W

@[simp] theorem select_row_group (hb : 0 < b) (hW : 0 < W) (i : Fin b) :
    select hb (row hW i) (group hW i) = i := by
  apply Fin.ext
  change ((group hW i).val * W + (row hW i).val) % b = _
  rw [group_mul_add_row, Nat.mod_eq_of_lt i.isLt]

theorem row_select (hb : 0 < b) (u : Fin W) (g : Fin (groups b W))
    (hg : g.val * W + u.val < b) : row (Nat.zero_lt_of_lt u.isLt) (select hb u g) = u := by
  apply Fin.ext
  simp [row, select, Nat.mod_eq_of_lt hg, Nat.add_mod, Nat.mod_eq_of_lt u.isLt]

theorem group_select (hb : 0 < b) (u : Fin W) (g : Fin (groups b W))
    (hg : g.val * W + u.val < b) : group (Nat.zero_lt_of_lt u.isLt) (select hb u g) = g := by
  apply Fin.ext
  change (g.val * W + u.val) % b / W = g.val
  rw [Nat.mod_eq_of_lt hg, Nat.mul_comm g.val W, Nat.mul_add_div (Nat.zero_lt_of_lt u.isLt),
    Nat.div_eq_of_lt u.isLt, Nat.add_zero]

/-- With the padded positions deleted, rearrangement is a bijection. -/
def genuineEquiv (hb : 0 < b) (hW : 0 < W) :
    Fin b ≃ {ug : Fin W × Fin (groups b W) // ug.2.val * W + ug.1.val < b} where
  toFun i := ⟨(row hW i, group hW i), by simpa only [group_mul_add_row] using i.isLt⟩
  invFun ug := select hb ug.val.1 ug.val.2
  left_inv := select_row_group hb hW
  right_inv := by
    rintro ⟨⟨u,g⟩, hg⟩
    exact Subtype.ext (Prod.ext (row_select hb u g hg) (group_select hb u g hg))

/-- Padded slots can occur only in the final group. -/
theorem final_group_of_padding (u : Fin W) (g : Fin (groups b W))
    (hpad : b ≤ g.val * W + u.val) : g.val + 1 = groups b W := by
  have hW := Nat.zero_lt_of_lt u.isLt
  have h : groups b W ≤ g.val + 1 := (ceilDiv_le_iff_le_mul hW).mpr (by
    rw [Nat.mul_add_one, Nat.mul_comm W g.val]
    exact hpad.trans (Nat.add_le_add_left u.isLt.le _))
  exact Nat.le_antisymm g.isLt h

/-- `P` arbitrary prefixes and `R` arbitrary suffix positions are spectators.
Every one of the `W` rows has volume `P * groups b W * R`. -/
theorem row_volume_le (hW : 0 < W) (hWb : W ≤ b) (P R : ℕ) :
    W * (P * groups b W * R) ≤ 2 * (P * b * R) := by
  calc
    _ = P * (W * groups b W) * R := by ac_rfl
    _ ≤ P * (2 * b) * R := Nat.mul_le_mul_right R
      (Nat.mul_le_mul_left P (groups_volume_le_twice hW hWb))
    _ = _ := by ac_rfl

end BatchRows

end NearSquareRoot
end Computability
end OAI
