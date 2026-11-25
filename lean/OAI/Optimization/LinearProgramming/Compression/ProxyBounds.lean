import OAI.Optimization.LinearProgramming.Compression.ProxyOracle
import Mathlib.Data.Nat.Size

/-! Exponent bounds for the mixed product and dependence on rational input length. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

private theorem nat_logb_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ Real.logb 2 (n : ℝ) ∧ Real.logb 2 (n : ℝ) ≤ n.size := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · exact Real.logb_nonneg (by norm_num) hn'
  · calc
      Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((2 : ℝ)^n.size) :=
        Real.logb_le_logb_of_le (by norm_num) (by linarith) (by exact_mod_cast (Nat.lt_size_self n).le)
      _ = _ := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- The absolute logarithm of a positive reduced rational is bounded by the length of
its signed numerator and positive denominator. -/
theorem abs_logb_le_rat_bits {q : ℚ} (hq : 0 < q) :
    |Real.logb 2 (q : ℝ)| ≤ (q.num.natAbs.size + q.den.size : ℕ) := by
  have hn := Rat.num_pos.mpr hq
  have ha : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hn.le
  have hn' : 1 ≤ q.num.natAbs := by omega
  have hd : 1 ≤ q.den := q.den_pos
  obtain ⟨h₁,h₂⟩ := nat_logb_bounds _ hn'
  obtain ⟨h₃,h₄⟩ := nat_logb_bounds _ hd
  have hnr : (q.num : ℝ) = (q.num.natAbs : ℝ) := calc
    _ = ((q.num.natAbs : ℤ) : ℝ) := congrArg (Int.cast : ℤ → ℝ) ha.symm
    _ = _ := Int.cast_natCast _
  have hz₁ : (q.num.natAbs : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn'
  have hz₂ : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  rw [Rat.cast_def, hnr, Real.logb_div hz₁ hz₂, abs_le]
  push_cast
  constructor <;> linarith

/-- On precisely the branch that constructs powers, even the numerical value of its cutoff
is bounded by the bit length of the magnitude that caused the branch. -/
theorem threshold_le_rat_bits_of_symbolic {fuel k : ℕ} {q : ℚ} (hq : 0 < q)
    (hsym : logProxyNumerator fuel k q = none) :
    2 ^ fuel ≤ q.num.natAbs.size + q.den.size := by
  have h := ((logProxyNumerator_eq_none_iff fuel k hq).mp hsym).trans (abs_logb_le_rat_bits hq)
  exact_mod_cast h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exponent of two after substituting grid numerators and clearing denominators is
controlled by the one-norm of the input form, independently of its number of terms. -/
theorem clearedProxyOffset_abs_le (large : Finset ι) (D : ℕ) {T A : ℤ} (hT : 1 ≤ T)
    (c : ℤ) (a grid : ι → ℤ) (hform : |c| + ∑ i, |a i| ≤ A)
    (hgrid : ∀ i ∉ large, |grid i| ≤ D * T) :
    |clearedProxyOffset large D c a grid| ≤ D * T * A := by
  let C := (D : ℤ) * T
  have hD : (0 : ℤ) ≤ D := by positivity
  have hC : 0 ≤ C := mul_nonneg hD (by omega)
  have hDC : (D : ℤ) ≤ C := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hT hD
  have hsum :
      ∑ i ∈ Finset.univ \ large, |a i * grid i| ≤ C * ∑ i, |a i| := calc
    _ ≤ ∑ i ∈ Finset.univ \ large, C * |a i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hgrid i (Finset.mem_sdiff.mp hi).2) (abs_nonneg _)
    _ ≤ ∑ i, C * |a i| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => mul_nonneg hC (abs_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm
  calc
    |clearedProxyOffset large D c a grid| ≤ |(D : ℤ) * c| +
        |∑ i ∈ Finset.univ \ large, a i * grid i| := abs_add_le _ _
    _ ≤ C * |c| + C * ∑ i, |a i| := by
      rw [abs_mul, abs_of_nonneg hD]
      exact add_le_add (mul_le_mul_of_nonneg_right hDC (abs_nonneg _))
        ((Finset.abs_sum_le_sum_abs _ _).trans hsum)
    _ = C * (|c| + ∑ i, |a i|) := (mul_add _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hform hC

/-- The uniform coefficient estimates used when evaluating an affine sign by powers.
Here `T=2^fuel`, `D=2^(k+2)`, and `2^k A ≤ T` is the manuscript's cutoff choice. -/
theorem logProxy_exponent_bounds (fuel k : ℕ) {A : ℤ} (c : ℤ) (a : ι → ℤ) (mag : ι → ℚ)
    (hm : ∀ i, 0 < mag i) (hform : |c| + ∑ i, |a i| ≤ A)
    (hcut : (2 : ℤ)^k * A ≤ 2^fuel) :
    let data i := logProxyNumerator fuel k (mag i)
    let large := Finset.univ.filter (fun i => data i = none)
    |clearedProxyOffset large (2^(k+2)) c a (fun i => (data i).getD 0)| ≤
        4 * ((2 : ℤ)^fuel)^2 ∧
    ∀ i, |((2 : ℤ)^(k+2)) * a i| ≤ 4 * (2 : ℤ)^fuel := by
  let data i := logProxyNumerator fuel k (mag i)
  let large := Finset.univ.filter (fun i => data i = none)
  let T := (2 : ℤ)^fuel
  let D := (2 : ℕ)^(k+2)
  have hT : 1 ≤ T := one_le_pow₀ (by norm_num)
  have hD : (0 : ℤ) ≤ D := by positivity
  have hDA : (D : ℤ) * A ≤ 4*T := by
    dsimp [D,T]
    rw [pow_add]
    nlinarith only [hcut]
  have hgrid (i) (hi : i ∉ large) : |(data i).getD 0| ≤ D * T := by
    have hn : data i ≠ none := by simpa [large] using hi
    cases he : data i with
    | none => contradiction
    | some u =>
      have hh := (logProxyNumerator_abs_lt fuel k (hm i) he).le
      simpa [D,T] using hh
  have ho := clearedProxyOffset_abs_le large D hT c a (fun i => (data i).getD 0) hform hgrid
  constructor
  · calc
      |clearedProxyOffset large D c a (fun i => (data i).getD 0)| ≤ D * T * A := ho
      _ = (D * A) * T := by ring
      _ ≤ (4*T) * T := mul_le_mul_of_nonneg_right hDA (by omega)
      _ = _ := by ring
  · intro i
    have hi : |a i| ≤ ∑ j, |a j| := Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    have hia : |a i| ≤ A := by linarith [abs_nonneg c]
    change |2^(k+2) * a i| ≤ 4*T
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2^(k+2))]
    have hcast : (2 : ℤ)^(k+2) = D := by simp [D]
    rw [hcast]
    exact (mul_le_mul_of_nonneg_left hia hD).trans hDA

end Compression
end LinearProgramming
end Optimization
end OAI
