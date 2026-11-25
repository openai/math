import OAI.LinearAlgebra.SpectralBooks.DimensionLaw
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Natural diagonal evaluations

Monotonicity on positive integer diagonals and multiplicativity force their
evaluation to be a single power, determined by the binary diagonal.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Real
open scoped NNReal

variable {A : Type*} [Semiring A] (v : A →* ℝ≥0)
  (hmono : ∀ {a b : ℕ}, 0 < a → a ≤ b → v (a : A) ≤ v (b : A))

include hmono in
theorem spectral_natCast_one_le (n : ℕ) (hn : 0 < n) : 1 ≤ v (n : A) := by
  simpa using hmono (a := 1) (b := n) (by decide) hn

include hmono in
/-- Positive integer diagonals have a nonnegative logarithmic price. -/
theorem spectral_natCast_logb_nonneg (n : ℕ) (hn : 0 < n) : 0 ≤ logb 2 (v (n : A)) :=
  logb_nonneg (by norm_num) (by exact_mod_cast spectral_natCast_one_le v hmono n hn)

include hmono in
private theorem spectral_natCast_logb_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    logb 2 (v (a : A)) ≤ logb 2 (v (b : A)) :=
  logb_le_logb_of_le (by norm_num)
    (by exact_mod_cast zero_lt_one.trans_le (spectral_natCast_one_le v hmono a ha))
    (by exact_mod_cast hmono ha hab)

include hmono in
/-- The logarithmic price of the `n`-diagonal is the binary price times
`log₂ n`. -/
theorem spectral_natCast_logb (n : ℕ) (hn : 0 < n) :
    logb 2 (v (n : A)) = logb 2 (v (2 : A)) * logb 2 n := by
  refine dimension_price_eq_logb (p := fun i => logb 2 (v (i : A)))
    (fun _ _ => spectral_natCast_logb_mono v hmono) (by simp) ?_ hn
  intro i j hi hj
  have hpos {k : ℕ} (hk : 0 < k) : (v (k : A) : ℝ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (spectral_natCast_one_le v hmono k hk)).ne'
  rw [Nat.cast_mul, map_mul, NNReal.coe_mul, logb_mul (hpos hi) (hpos hj)]

include hmono in
/-- The diagonal exponent is `log₂(v 2)` over every semiring carrying a
monotone multiplicative evaluation on positive integer diagonals. -/
theorem spectral_natCast_eq_rpow (n : ℕ) (hn : 0 < n) :
    v (n : A) = (n : ℝ≥0) ^ logb 2 (v (2 : A)) := by
  apply NNReal.eq
  rw [NNReal.coe_rpow, NNReal.coe_natCast]
  have hv : 0 < (v (n : A) : ℝ) := by
    exact_mod_cast zero_lt_one.trans_le (spectral_natCast_one_le v hmono n hn)
  apply (Real.strictMonoOn_logb (by norm_num : (1 : ℝ) < 2)).injOn
      (show 0 < (v (n : A) : ℝ) from hv) (Real.rpow_pos_of_pos (by exact_mod_cast hn : 0 < (n : ℝ)) _)
  rw [Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]
  exact spectral_natCast_logb v hmono n hn

end SpectralBooks
end LinearAlgebra
end OAI
