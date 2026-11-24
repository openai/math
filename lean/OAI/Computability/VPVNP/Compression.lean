import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Iterating the wire energy estimate

Equation (7.4) of *VP and VNP differ over every field* follows from the
energy estimate for one block and the geometric decrease in the number of
positions. The bound below gives the constant multiplying the initial
position count explicitly.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open scoped BigOperators

/-- With positive wire masses of total one, the energy controls total width. -/
theorem widthSum_le_sqrtEnergy {Wire : Type*} [Fintype Wire]
    (width mass : Wire → ℝ) (hpos : ∀ e, 0 < mass e) (htotal : ∑ e, mass e = 1) :
    ∑ e, width e ≤ Real.sqrt (∑ e, width e ^ 2 / mass e) := by
  apply Real.le_sqrt_of_sq_le
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ width (fun i _ => hpos i)
  simpa only [htotal, div_one] using h

/-- Multiplication by `4^i` makes the one-block estimates telescope. The term
from block `i` then has ratio `4/κ²` to the corresponding term from block
`i-1`. Only the estimates before the specified horizon are needed. -/
theorem scaledEnergy_le (L : ℕ → ℝ) (P c κ : ℝ) (T : ℕ)
    (hstep : ∀ i < T, L (i + 1) ≤ L i / 4 + c * (P / κ ^ i) ^ 2) :
    4 ^ T * L T ≤ L 0 + 4 * c * P ^ 2 * ∑ i ∈ Finset.range T, (4 / κ ^ 2) ^ i := by
  induction T with
  | zero => simp
  | succ t ih =>
    have hprev := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hblock := mul_le_mul_of_nonneg_left (hstep t (Nat.lt_succ_self _))
      (by positivity : 0 ≤ (4 : ℝ) ^ (t + 1))
    have hpow : (κ ^ t) ^ 2 = (κ ^ 2) ^ t := by rw [← pow_mul, Nat.mul_comm, pow_mul]
    rw [Finset.sum_range_succ, mul_add, ← add_assoc]
    refine hblock.trans (le_trans ?_ (add_le_add_left hprev _))
    rw [pow_succ, div_pow, div_pow, hpow]
    exact le_of_eq (by ring)

/-- Equation (7.4), with an error coefficient independent of the number
of blocks. Here `P / κ^i` is the position count at the start of block `i`. -/
theorem sqrtEnergy_le (L : ℕ → ℝ) {P c κ : ℝ} (T : ℕ)
    (hP : 0 ≤ P) (hc : 0 ≤ c) (hκ : 2 < κ) (hinit : 0 ≤ L 0)
    (hstep : ∀ i < T, L (i + 1) ≤ L i / 4 + c * (P / κ ^ i) ^ 2) :
    Real.sqrt (L T) ≤ (Real.sqrt (L 0) + P * Real.sqrt (4 * c / (1 - 4 / κ ^ 2))) / 2 ^ T := by
  let r := 4 / κ ^ 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr' : r < 1 := by
    apply (div_lt_iff₀ (by nlinarith : 0 < κ ^ 2)).mpr
    nlinarith [sq_nonneg (κ - 2)]
  have hsum : ∑ i ∈ Finset.range T, r ^ i ≤ 1 / (1 - r) := by
    simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := T) hr hr')
  have hscaled := scaledEnergy_le L P c κ T hstep
  have hbound : 4 ^ T * L T ≤ L 0 + P ^ 2 * (4 * c / (1 - r)) := by
    calc
      _ ≤ L 0 + 4 * c * P ^ 2 * ∑ i ∈ Finset.range T, r ^ i := hscaled
      _ ≤ L 0 + 4 * c * P ^ 2 * (1 / (1 - r)) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hsum (by positivity)) _
      _ = _ := by ring
  have hs : 0 ≤ 4 * c / (1 - r) := div_nonneg (by positivity) (sub_nonneg.mpr hr'.le)
  change Real.sqrt (L T) ≤ (Real.sqrt (L 0) + P * Real.sqrt (4 * c / (1 - r))) / 2 ^ T
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [div_pow, ← pow_mul, Nat.mul_comm T 2, pow_mul]
  norm_num
  apply (le_div_iff₀ (by positivity)).mpr
  rw [mul_comm]
  calc
    _ ≤ L 0 + P ^ 2 * (4 * c / (1 - r)) := hbound
    _ ≤ _ := by
      rw [add_sq, mul_pow, Real.sq_sqrt hinit, Real.sq_sqrt hs]
      linarith [mul_nonneg (Real.sqrt_nonneg (L 0))
        (mul_nonneg hP (Real.sqrt_nonneg (4 * c / (1 - r))))]

end Compression

end VPVNP
end Computability
end OAI
