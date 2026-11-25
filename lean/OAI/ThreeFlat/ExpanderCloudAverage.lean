import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

namespace OAI
/-! # Scalar normalizations for integral walk averages -/

namespace ThreeFlat

/-- Putting the first `t` powers of a transition matrix over a common
denominator multiplies its summand for the `k+1` step walk by this weight. -/
theorem cloudAverage_weight {b t k : ℕ} (hb : 0 < b) (ht : 0 < t) (hk : k < t) :
    1 / ((t : ℝ) * (b : ℝ) ^ t) * (↑(b ^ (t - (k + 1))) : ℝ) =
      (1 / (t : ℝ)) * (1 / (b : ℝ)) ^ (k + 1) := by
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  rw [Nat.cast_pow, one_div_pow]
  field_simp
  rw [← pow_add, Nat.sub_add_cancel hk]

/-- Scaling a numerator of denominator `d` to any positive multiple `q`
preserves its normalized weight. -/
theorem cloudAverage_dvd {q d : ℕ} (hq : 0 < q) (hd : 0 < d) (h : d ∣ q) :
    (↑(q / d) : ℝ) / (q : ℝ) = 1 / (d : ℝ) := by
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr hq.ne') (Nat.cast_ne_zero.mpr hd.ne')).mpr
  rw [one_mul, ← Nat.cast_mul, Nat.div_mul_cancel h]

end ThreeFlat

end OAI
