import Lean.Elab.Tactic.Omega

namespace OAI
/-! # The numerical rank budget for block replacement

Here the tick count is `T = 2^(w^6)`, the number of teams is `q = 2^(w^3)`,
and the volume is `V = 2^(w^10)`. The exponent saved in each fixing is
`q * V / 2^w`. It exceeds the sum of the exponents spent on the block
count and on all the fixings for any polynomially bounded block length.
-/

namespace ThreeFlat.Diagonal

/-- Uniform binary exponential bound for every polynomial exponent at most the width. -/
theorem width_pow_le_two_pow_sq {w k : Nat} (hk : k ≤ w) : w ^ k ≤ 2 ^ (w ^ 2) := by
  calc
    w ^ k ≤ (2 ^ w) ^ k := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) _
    _ = 2 ^ (w * k) := (Nat.pow_mul _ _ _).symm
    _ ≤ 2 ^ (w ^ 2) := Nat.pow_le_pow_right (by decide) (by
      simpa [Nat.pow_succ] using Nat.mul_le_mul_left w hk)

/-- Even the full transition count and every fixing fit inside the saved exponent.
The statement applies to all sufficiently large natural widths, including dyadic ones. -/
theorem defect_exponent_budget {w d L : Nat} (hw : d + 8 ≤ w) (hL : L ≤ w ^ d) :
    w ^ 6 + 4 * L * 2 ^ (w ^ 10 - w ^ 4) < 2 ^ (w ^ 3) * 2 ^ (w ^ 10 - w) := by
  have hw2 : 3 ≤ w ^ 2 := Nat.le_trans (by omega : 3 ≤ w) (Nat.le_self_pow (by decide) w)
  have hcubic : w ^ 2 + 3 ≤ w ^ 3 := by
    have h := Nat.mul_le_mul_left (w ^ 2) (by omega : 2 ≤ w)
    rw [Nat.pow_succ w 2]
    omega
  have hsum : w ^ 6 + 4 * L < 2 ^ (w ^ 3) := by
    have h₁ := width_pow_le_two_pow_sq (by omega : 6 ≤ w)
    have h₂ := Nat.le_trans hL (width_pow_le_two_pow_sq (by omega : d ≤ w))
    calc
      w ^ 6 + 4 * L < 2 ^ (w ^ 2) * 8 := by
        have := Nat.two_pow_pos (w ^ 2)
        omega
      _ = 2 ^ (w ^ 2 + 3) := (Nat.pow_add 2 _ 3).symm
      _ ≤ 2 ^ (w ^ 3) := Nat.pow_le_pow_right (by decide) hcubic
  let rem := 2 ^ (w ^ 10 - w)
  have hrem : 0 < rem := Nat.two_pow_pos _
  have hchunk : 2 ^ (w ^ 10 - w ^ 4) ≤ rem := by
    exact Nat.pow_le_pow_right (by decide)
      (Nat.sub_le_sub_left (Nat.le_self_pow (by decide) w) _)
  calc
    _ ≤ w ^ 6 * rem + 4 * L * rem := Nat.add_le_add
      (Nat.le_mul_of_pos_right _ hrem) (Nat.mul_le_mul_left _ hchunk)
    _ = (w ^ 6 + 4 * L) * rem := (Nat.add_mul _ _ _).symm
    _ < _ := Nat.mul_lt_mul_of_pos_right hsum hrem

/-- An exponent saving larger than the fixing overhead makes the total
rank error strictly smaller than the external dimension. -/
theorem defect_dimension_budget {w d L B : Nat} (hw : d + 8 ≤ w) (hL : L ≤ w ^ d)
    (hB : 2 ^ (w ^ 3) * 2 ^ (w ^ 10 - w) ≤ B) :
    (2 ^ (w ^ 6) / L) * 2 ^ (4 * L * 2 ^ (w ^ 10 - w ^ 4)) *
      2 ^ (B - 2 ^ (w ^ 3) * 2 ^ (w ^ 10 - w)) < 2 ^ B := by
  have h := defect_exponent_budget hw hL
  apply Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.div_le_self (2 ^ (w ^ 6)) L)))
  rw [← Nat.pow_add, ← Nat.pow_add]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

/-- The catalytic-collapse parameter choices guarantee the external register is
large enough to realize the saving. This gives the strict dimension estimate
without any separate bound on the memory size. -/
theorem collapse_defect_dimension {w d L A : Nat} (hw : d + 8 ≤ w)
    (hmin : w ^ (A + 10) ≤ L) (hmax : L ≤ w ^ d) :
    let V := 2 ^ (w ^ 10)
    let q := 2 ^ (w ^ 3)
    let B := 2 * (q * V * L / w ^ (A + 2))
    let a := 2 ^ (w ^ 10 - w ^ 4)
    (2 ^ (w ^ 6) / L) * 2 ^ (4 * L * a) * 2 ^ (B - q * 2 ^ (w ^ 10 - w)) < 2 ^ B := by
  dsimp only
  apply defect_dimension_budget hw hmax
  have hwpos : 0 < w := by omega
  have hden : w ^ (A + 2) ≤ L :=
    Nat.le_trans (Nat.pow_le_pow_right hwpos (by omega : A + 2 ≤ A + 10)) hmin
  have hfull : 2 ^ (w ^ 3) * 2 ^ (w ^ 10) ≤
      2 ^ (w ^ 3) * 2 ^ (w ^ 10) * L / w ^ (A + 2) :=
    (Nat.le_div_iff_mul_le (Nat.pow_pos hwpos)).mpr (Nat.mul_le_mul_left _ hden)
  have hsave := Nat.mul_le_mul_left (2 ^ (w ^ 3))
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le (w ^ 10) w))
  omega

end ThreeFlat.Diagonal

end OAI
