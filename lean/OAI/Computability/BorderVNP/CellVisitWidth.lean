import OAI.Computability.BorderVNP.CellVisitClock
import OAI.Computability.BorderVNP.TeamScales

/-! # Binary width of polynomially bounded private loop and address fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open RationalHitting

/-- Bounding a natural by a fixed polynomial costs only linearly many digits in the
binary width of its argument, with the actual leading coefficient and exponent accounted for. -/
theorem size_of_polynomial_field {x n C k : ℕ} (hx : x ≤ C*(n+2)^k) :
    x.size ≤ C.size + k*(n.size+1) := by
  have hb : n+2 ≤ 2^(n.size+1) := by
    have h := Nat.lt_size_self n
    have hp : 0 < 2^n.size := pow_pos (by decide) _
    rw [pow_succ]
    omega
  rw [Nat.size_le,pow_add,Nat.mul_comm k (n.size+1),pow_mul]
  exact hx.trans_lt ((Nat.mul_le_mul_left C (Nat.pow_le_pow_left hb k)).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self C) (pow_pos (pow_pos (by decide) _) _)))

/-- One polynomial in the base parameter's binary width suffices for all lexical and
arithmetic visits when the largest literal and largest actual counter have polynomial bounds. -/
theorem visitClock_polynomial_fields (d h J C₁ k₁ C₂ k₂ : ℕ) :
    ∃ A k : ℕ, 0 < A ∧ 0 < k ∧ ∀ n M U : ℕ,
      M ≤ C₁*(n+2)^k₁ → U ≤ C₂*(n+2)^k₂ →
      (visitClock d h).eval (visitWidth M U J) ≤ A*(n.size+1)^k := by
  let B := 1+J+C₁.size+C₂.size+k₁+k₂
  obtain ⟨A,k,hA,hk,growth⟩ := (visitClock d h).growth
  refine ⟨A*B^k,k,Nat.mul_pos hA (pow_pos (show 0 < B by dsimp [B]; omega) _),hk,?_⟩
  intro n M U hM hU
  have bm := size_of_polynomial_field hM
  have bu := size_of_polynomial_field hU
  have w : visitWidth M U J ≤ B*(n.size+1) := by
    dsimp [B,visitWidth]
    simp only [Nat.add_mul,Nat.one_mul,Nat.mul_add,Nat.mul_one] at *
    omega
  have h := growth (visitWidth M U J) (by dsimp [visitWidth]; omega)
  apply h.trans
  calc A*(visitWidth M U J)^k ≤ A*(B*(n.size+1))^k :=
         Nat.mul_le_mul_left _ (Nat.pow_le_pow_left w _)
       _ = _ := by rw [mul_pow,Nat.mul_assoc]

/-- Every input dimension fits in the physical logarithmic width, for every positive batch
count, including the zero-dimensional input. -/
theorem size_le_logWidth (n r : ℕ) (hr : 1 ≤ r) : n.size ≤ TeamScales.logWidth r n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  have npos : 0 < (n : ℝ) := by exact_mod_cast hn
  have rone : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have x : 0 < 2*(n : ℝ)*r := by positivity
  have ceil : Real.logb 2 (2*(n : ℝ)*r) ≤ (TeamScales.logWidth r n : ℝ) := Nat.le_ceil _
  have bound := (Real.logb_le_iff_le_rpow (by norm_num : 1 < (2 : ℝ)) x).mp ceil
  rw [Real.rpow_natCast] at bound
  have strict : (n : ℝ) < 2*(n : ℝ)*r := by nlinarith only [npos, mul_nonneg npos.le (sub_nonneg.mpr rone)]
  rw [Nat.size_le]
  exact_mod_cast strict.trans_le bound

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
