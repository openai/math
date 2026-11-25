import OAI.Optimization.LinearProgramming.Compression.BinarySerialization
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OracleSpec.MinorLog

theorem integerDigit_cases (a i : ℕ) : integerDigit a i = 0 ∨ integerDigit a i = 1 := by
  have h : integerDigit a i < 2 := Nat.mod_lt _ (by decide)
  omega

theorem integerDigit_testBit (a i : ℕ) : integerDigit a i = (a.testBit i).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change integerDigit a i = (decide (integerDigit a i = 1)).toNat
  rcases integerDigit_cases a i with h | h <;> simp [h]

/-- The public width of the prefix grows precisely on a set bit. In particular zero,
including the empty prefix, always has width one. -/
theorem width_mod_pow_succ (a i : ℕ) : width (a % 2^(i+1)) =
    if integerDigit a i = 0 then width (a % 2^i) else i+1 := by
  have hs : a % 2^(i+1) = a % 2^i + integerDigit a i * 2^i := by
    rw [← sum_integerDigits,Finset.sum_range_succ,sum_integerDigits]
  rcases integerDigit_cases a i with h | h
  · simp [hs,h]
  · simp only [h,one_ne_zero,ite_false,hs,one_mul]
    have pos : 0 < 2^i := by positivity
    have lo : 2^i ≤ a % 2^i+2^i := by omega
    have up : a % 2^i+2^i < 2^(i+1) := by
      have := Nat.mod_lt a pos; rw [pow_succ]; omega
    unfold width
    rw [(Nat.log2_eq_iff (n := a % 2^i+2^i) (k := i) (by omega)).mpr ⟨lo,up⟩]

theorem width_of_lt_pow {a k : ℕ} (ha : a < 2^k) (hk : 0 < k) : width a ≤ k := by
  unfold width
  by_cases hz : a = 0
  · simp [hz]; omega
  · exact (Nat.log2_lt hz).mpr ha

end Compression
end LinearProgramming
end Optimization
end OAI
