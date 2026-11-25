import OAI.LinearAlgebra.SpectralBooks.PolynomialOverhead
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Logarithmic dependence on wire dimension

Restricting a wire to fewer labels is monotone, and tensoring wires multiplies
the number of labels. Comparing powers with consecutive powers of two then
determines every positive-dimensional value from the binary wire.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- Every nondecreasing wire price that adds on products of positive dimensions
equals its binary price times the logarithm of the dimension. -/
theorem dimension_price_eq_logb {p : ℕ → ℝ} (hmono : ∀ i j, 0 < i → i ≤ j → p i ≤ p j)
    (hone : p 1 = 0) (hmul : ∀ i j, 0 < i → 0 < j → p (i * j) = p i + p j)
    {q : ℕ} (hq : 0 < q) : p q = p 2 * Real.logb 2 q := by
  have hp (i : ℕ) (hi : 0 < i) (n : ℕ) : p (i ^ n) = n * p i := by
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, hmul _ _ (pow_pos hi _) hi, ih, Nat.cast_succ, add_mul, one_mul]
  have hp2 : 0 ≤ p 2 := by simpa [hone] using hmono 1 2 (by decide) (by decide)
  have happrox (k : ℕ) : k * p q ≤ k * (p 2 * Real.logb 2 q) + p 2 ∧
      k * (p 2 * Real.logb 2 q) ≤ k * p q + p 2 := by
    let b := Nat.log 2 (q ^ k)
    have hlo : 2 ^ b ≤ q ^ k := Nat.pow_log_le_self _ (pow_pos hq _).ne'
    have hhi : q ^ k ≤ 2 ^ (b + 1) := (Nat.lt_pow_succ_log_self (by decide) _).le
    have hplo := hmono _ _ (pow_pos (by decide : 0 < 2) _) hlo
    have hphi := hmono _ _ (pow_pos hq _) hhi
    rw [hp _ (by decide) _, hp _ hq _] at hplo
    rw [hp _ hq _, hp _ (by decide) _, Nat.cast_add_one] at hphi
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (2 : ℝ) ^ b) (by exact_mod_cast hlo : (2 : ℝ)^b ≤ (q : ℝ)^k)
    have hu := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (q : ℝ)^k) (by exact_mod_cast hhi : (q : ℝ)^k ≤ (2 : ℝ)^(b+1))
    simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      Nat.cast_add_one, mul_one] at hl hu
    constructor <;> nlinarith only [hphi, hplo, mul_le_mul_of_nonneg_left hl hp2,
      mul_le_mul_of_nonneg_left hu hp2]
  apply eq_of_nat_mul_close (C := p 2)
  intro k
  rw [abs_le, mul_sub]
  obtain ⟨hu, hl⟩ := happrox k
  constructor <;> linarith

/-- Its multiplicative form applies to the normalized spectral value of a wire,
or of square matrix multiplication as a function of its order. -/
theorem dimension_value_eq_rpow {v : ℕ → ℝ} (hmono : Monotone v) (hone : v 1 = 1)
    (hmul : ∀ m n, v (m * n) = v m * v n) {q : ℕ} (hq : 0 < q) :
    v q = (q : ℝ) ^ (Real.logb 2 (v 2)) := by
  have hpos (n : ℕ) (hn : 0 < n) : 0 < v n := by
    have h := hmono (show 1 ≤ n from hn)
    linarith
  have h := dimension_price_eq_logb (p := fun n => Real.logb 2 (v n))
    (fun i j hi hij => Real.logb_le_logb_of_le (by norm_num) (hpos i hi) (hmono hij))
    (by simp [hone]) (fun i j hi hj => by rw [hmul, Real.logb_mul (hpos _ hi).ne' (hpos _ hj).ne']) hq
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hr := Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (hpos q hq)
  have hR := Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    (Real.rpow_pos_of_pos hq' (Real.logb 2 (v 2)))
  rw [Real.logb_rpow_eq_mul_logb_of_pos hq', ← h] at hR
  exact hr.symm.trans hR

end SpectralBooks
end LinearAlgebra
end OAI
