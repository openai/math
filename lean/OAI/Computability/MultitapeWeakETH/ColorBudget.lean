import OAI.Computability.MultitapeWeakETH.Coloring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # A quantitative union bound for the column coloring -/

namespace OAI.Computability.MultitapeWeakETH

/-- A fixed color misses all M candidates with probability at most
exp(-M/k). This criterion discharges the finite cardinality comparison. -/
theorem coloring_budget_of_exp {p k M N : ℕ} (hk : 0 < k) (size : M ≤ N)
    (budget : (p:ℝ)*k < Real.exp ((M:ℝ)/k)) :
    (p*k)*((k-1)^M*k^(N-M)) < k^N := by
  have pos : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have one : (1:ℝ) ≤ k := by exact_mod_cast hk
  have avoid : ((k:ℝ)-1)/k ≤ Real.exp (-(k:ℝ)⁻¹) := by
    calc
      _ = -(k:ℝ)⁻¹+1 := by field_simp; ring
      _ ≤ _ := Real.add_one_le_exp _
  have power := pow_le_pow_left₀ (div_nonneg (by linarith) pos.le) avoid M
  rw [div_pow,← Real.exp_nat_mul] at power
  have mass : (p:ℝ)*k * (((k:ℝ)-1)^M/(k:ℝ)^M) < 1 := by
    calc
      _ ≤ (p:ℝ)*k * Real.exp ((M:ℝ) * -(k:ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left power (mul_nonneg (Nat.cast_nonneg _) pos.le)
      _ < Real.exp ((M:ℝ)/k) * Real.exp ((M:ℝ) * -(k:ℝ)⁻¹) :=
        mul_lt_mul_of_pos_right budget (Real.exp_pos _)
      _ = 1 := by rw [← Real.exp_add,div_eq_mul_inv,← mul_add,add_neg_cancel,mul_zero,Real.exp_zero]
  rw [← mul_div_assoc,div_lt_iff₀ (pow_pos pos M),one_mul] at mass
  have strict := mul_lt_mul_of_pos_right mass (pow_pos pos (N-M))
  rw [← pow_add, Nat.add_sub_of_le size] at strict
  have casted : ((p*k)*((k-1)^M*k^(N-M)) : ℕ) < (k^N : ℝ) := by
    push_cast [Nat.cast_sub (show 1 ≤ k from hk)]
    simpa only [mul_assoc] using strict
  exact_mod_cast casted

/-- For r repetitions and j previous binary coordinates, there are at most
2^(r*j) prefixes. Any k at most 2^r with k*r² ≤ M meets the union bound as
soon as r exceeds j+1. -/
theorem coloring_budget_for_columns {p k M r j : ℕ} (hk : 0 < k)
    (prefixes : p ≤ 2^(r*j)) (colors : k ≤ 2^r) (size : M ≤ 2^r)
    (room : k*r^2 ≤ M) (large : j+1 < r) :
    (p*k)*((k-1)^M*k^(2^r-M)) < k^(2^r) := by
  apply coloring_budget_of_exp hk size
  have pos : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have prod : p*k ≤ 2^(r*(j+1)) := by
    simpa only [Nat.mul_add,Nat.mul_one,pow_add] using Nat.mul_le_mul prefixes colors
  have e : (2:ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp 1]
  calc
    (p:ℝ)*k ≤ (2:ℝ)^(r*(j+1)) := by exact_mod_cast prod
    _ ≤ (Real.exp 1)^(r*(j+1)) := pow_le_pow_left₀ (by norm_num) e _
    _ = Real.exp (r*(j+1:ℝ)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    _ < Real.exp ((M:ℝ)/k) := by
      apply Real.exp_lt_exp.mpr
      apply (lt_div_iff₀ pos).mpr
      have lt : r*(j+1)*k < M := by
        calc
          _ < r*r*k := Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left large (by omega)) hk
          _ ≤ M := by simpa only [sq,Nat.mul_comm k] using room
      exact_mod_cast lt

end OAI.Computability.MultitapeWeakETH
