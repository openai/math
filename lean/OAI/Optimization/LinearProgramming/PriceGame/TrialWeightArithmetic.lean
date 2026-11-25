import OAI.Optimization.LinearProgramming.PriceGame.TrialMarketDataBounds
import Mathlib.Data.Nat.Log

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open Moment

/-- The fixed binary width of the rational learning-rate denominator, independent of the input. -/
def learningRateBits : ℕ := etaQ.den.size

private theorem log2_bound_of_le_two_pow {n k : ℕ} (h : n ≤ 2 ^ k) : n.log2 ≤ k := by
  have hl : n.log2 ≤ (2 ^ k).log2 := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right h
  simpa only [Nat.log2_two_pow] using hl

/-- Reduced numerator and denominator budgets for a positive-scale rational, including zero. -/
theorem dyadic_encoding_bounds (x : ℚ) (Q b d : ℕ) (hQ : 0 < Q) (hcap : Q ≤ 2 ^ d)
    (hden : x.den ∣ Q) (hmag : |x| ≤ (2 : ℚ) ^ b) :
    x.num.natAbs ≤ 2 ^ (b + d) ∧ x.den ≤ 2 ^ d ∧ RAM.ratBits x ≤ 3 + b + 2*d := by
  have hm : |x| ≤ ((2 ^ b : ℕ) : ℚ) := by simpa using hmag
  have hh := rat_num_abs_le_of_den_dvd x (2 ^ b) Q hQ hm hden
  have hnum : x.num.natAbs ≤ 2 ^ (b+d) := by
    rw [pow_add]
    exact hh.trans (Nat.mul_le_mul_left _ hcap)
  have hd := (Nat.le_of_dvd hQ hden).trans hcap
  refine ⟨hnum, hd, ?_⟩
  unfold RAM.ratBits
  have h1 := log2_bound_of_le_two_pow hnum
  have h2 := log2_bound_of_le_two_pow hd
  omega

theorem local_denominator_dyadic_bound (Q d r t : ℕ) (hQ : Q ≤ 2 ^ d) :
    Q * etaQ.den ^ min t r ≤ 2 ^ (d + learningRateBits*r) := by
  rw [pow_add, pow_mul]
  apply Nat.mul_le_mul hQ
  calc
    _ ≤ (2^learningRateBits)^(min t r) := Nat.pow_le_pow_left (Nat.lt_size_self etaQ.den).le _
    _ ≤ _ := Nat.pow_le_pow_right (Nat.two_pow_pos _) (Nat.min_le_right _ _)

/-- Per-element input rather than an average or an abstract transient-state cap. -/
structure WeightInputCap {ne : ℕ} (Q b : ℕ) (w : Weights ne) : Prop where
  den : ∀ e, (w e).den ∣ Q
  upper : ∀ e, w e ≤ (2 : ℚ) ^ b

theorem WeightInputCap.ratBits {ne Q b : ℕ} {w : Weights ne} (h : WeightInputCap Q b w)
    {d : ℕ} (hQ : 0 < Q) (hcap : Q ≤ 2^d) (hw : ∀ e, 0 ≤ w e) (e : Fin ne) :
    RAM.ratBits (w e) ≤ 3+b+2*d :=
  (dyadic_encoding_bounds _ Q b d hQ hcap (h.den e) (by simpa [abs_of_nonneg (hw e)] using h.upper e)).2.2

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
