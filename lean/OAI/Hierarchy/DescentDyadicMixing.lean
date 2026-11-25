import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI
/-! # The dyadic level budget in the old-block mixing estimate -/

namespace Hierarchy.DescentBaseVariance

open scoped BigOperators

/-- The finite level sum is bounded uniformly in the number of levels.
The change from the variance estimate to the off-diagonal estimate occurs
at the dyadic exponent of the chosen amplification factor. -/
theorem dyadic_level_sum (r : ℝ) (hr : 1<r) (hlt : r<2) (k N : ℕ) :
    (∑ s ∈ Finset.range N,r^s*min (1/(2:ℝ)^k) (1/(2:ℝ)^s)) ≤
    (r/2)^k*(1/(r-1) + 1/(1-r/2)) := by
  have r0 : 0<r := by linarith
  have ratio : 0<r/2 := by positivity
  have gap : 0<1-r/2 := by linarith
  have increase : 0<r-1 := by linarith
  let cost (s : ℕ) : ℝ := r^s*min (1/(2:ℝ)^k) (1/(2:ℝ)^s)
  have extend : ∑ s ∈ Finset.range N,cost s ≤ ∑ s ∈ Finset.range (k+N),cost s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun s _ _=>by
      dsimp [cost]
      exact mul_nonneg (pow_nonneg r0.le _) (le_min (by positivity) (by positivity)))
  have left : (∑ s ∈ Finset.range k,cost s) ≤ (r/2)^k/(r-1) := by
    calc
      _ ≤ ∑ s ∈ Finset.range k,r^s*(1/2^k) := Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (min_le_left _ _) (pow_nonneg r0.le s)
      _ = (∑ s ∈ Finset.range k,r^s)/2^k := by simp only [←Finset.sum_mul,div_eq_mul_inv,one_mul]
      _ ≤ _ := by
        rw [div_pow]
        apply (div_le_div_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) k) increase).mpr
        have identity := geom_sum_mul r k
        have den : (r^k/(2:ℝ)^k) * 2^k = r^k := by field_simp
        linarith
  have right : (∑ s ∈ Finset.range N,cost (k+s)) ≤ (r/2)^k/(1-r/2) := by
    calc
      _ ≤ ∑ s ∈ Finset.range N,r^(k+s)*(1/2^(k+s)) := Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg r0.le _)
      _ = (r/2)^k * ∑ s ∈ Finset.range N,(r/2)^s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [←pow_add,div_pow]
        ring
      _ ≤ _ := by
        have geometric : (∑ s ∈ Finset.range N,(r/2)^s) ≤ 1/(1-r/2) := by
          apply (le_div_iff₀ gap).mpr
          have identity := geom_sum_mul_neg (r/2) N
          linarith [pow_nonneg ratio.le N]
        simpa only [div_eq_mul_inv,one_mul] using
          mul_le_mul_of_nonneg_left geometric (pow_nonneg ratio.le k)
  calc
    _ ≤ _ := extend
    _ = _ := Finset.sum_range_add cost k N
    _ ≤ _ := add_le_add left right
    _ = _ := by ring

/-- A rounded propagation weight grows by at most twice the eighth-root
geometric sequence. -/
theorem ceil_weight (r : ℝ) (hr : 1≤r) (h8 : r^8=2) (s : ℕ) :
    (2:ℝ)^((s+7)/8) ≤ 2*r^s := by
  calc
    (2:ℝ)^((s+7)/8) = r^(8*((s+7)/8)) := by rw [pow_mul,h8]
    _ ≤ r^(8+s) := pow_le_pow_right₀ hr (by omega)
    _ = 2*r^s := by rw [pow_add,h8]

/-- The factor F to the minus seven eighths, in dyadic coordinates. -/
theorem root_eighth_decay (k : ℕ) :
    (((2:ℝ)^(1/8:ℝ))/2)^k = ((2:ℝ)^k)^(-(7/8):ℝ) := by
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)]
  have root : (2:ℝ)^(1/8:ℝ)/2 = (2:ℝ)^(-(7/8):ℝ) := by
    rw [show -(7/8:ℝ)=(1/8:ℝ)-1 by norm_num,Real.rpow_sub (by norm_num : 0<(2:ℝ)),Real.rpow_one]
  rw [root,←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2),mul_comm]

end Hierarchy.DescentBaseVariance

end OAI
