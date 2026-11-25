import OAI.Computability.IntegerMultiplication.Param.Costs
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Star
noncomputable section
open Filter Finset Real
abbrev drop_ (n:ℕ):ℝ := (1/2:ℝ)^n
theorem drop_p (n:ℕ) : 0 < drop_ n := pow_pos (by norm_num) _
theorem drop1 (n:ℕ) : drop_ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
theorem drop_le {m n} (h:m≤n) : drop_ n≤drop_ m :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

abbrev atan0 (x:ℝ) (i:ℕ) := (-1:ℝ)^i*x^(2*i+1) / ((2*i+1:ℕ):ℝ)
def arc (x:ℝ) (n:ℕ):ℝ :=
  ∑ i:Fin n, atan0 x i.val

theorem circle {x:ℝ} (h : |x|≤1/2) (n:ℕ) :
    |arc x n-Real.arctan x| ≤ 2*drop_ n := by
  have P : ‖x‖<1 := by rw [Real.norm_eq_abs]; linarith
  let f := atan0 x
  have ht := Real.hasSum_arctan P
  change HasSum f _ at ht
  have eq : arc x n=∑ i∈Finset.range n, f i := Fin.sum_univ_eq_sum_range _ _
  rw [eq,← ht.tsum_eq, ← ht.summable.sum_add_tsum_nat_add n]
  rw [show (∑ i∈Finset.range n,f i) -(∑ i∈Finset.range n,f i + ∑' i:ℕ, f (i+n)) = -(∑' i:ℕ, f (i+n)) from by abel]
  -- parse check
  let r:ℝ := 1/2
  have hgeo : |r| < 1 := by unfold r; norm_num
  let g (i:ℕ):ℝ := r^(i+n)
  have G : Summable g := by
    unfold g; simp_rw [pow_add]
    exact (summable_geometric_of_abs_lt_one hgeo).mul_right _
  have R i : ‖f (i+n)‖ ≤ g i := by
    unfold f atan0 g
    rw [Real.norm_eq_abs,abs_div,abs_mul,abs_pow,abs_pow]
    simp only [abs_neg,abs_one,one_pow,one_mul]
    have z : (0:ℝ) < ((2*(i+n)+1:ℕ):ℝ) := by positivity
    rw [abs_of_pos z,div_le_iff₀ z]
    have a : |x|^(2*(i+n)+1) ≤ drop_ (i+n) :=
      (pow_le_pow_left₀ (abs_nonneg x) h _).trans (drop_le (by omega))
    exact a.trans (le_mul_of_one_le_right (drop_p _).le (by push_cast; nlinarith))
  have V : Summable (fun i:ℕ=> ‖f (i+n)‖) :=
    G.of_nonneg_of_le (fun i=>norm_nonneg _) R
  refine le_trans ?_ (V.tsum_mono G R |>.trans (le_of_eq (b:=2*drop_ n) ?_))
  · rw [abs_neg,← Real.norm_eq_abs]
    exact norm_tsum_le_tsum_norm V
  unfold g; simp_rw [pow_add]
  rw [tsum_mul_right,tsum_geometric_of_abs_lt_one hgeo]
  unfold r; norm_num

theorem arc_cost (m:ℕ) (n:ℕ) (h:2≤ m) :
    |arc (m:ℝ)⁻¹ n-arctan (m:ℝ)⁻¹| ≤ 2*drop_ n :=
  circle (by
    have e : (2:ℝ)≤ m := by exact_mod_cast h
    rw [abs_of_nonneg (by positivity)]
    rw [one_div]
    exact inv_anti₀ (by norm_num) e) n

noncomputable def polestar (n:ℕ) :=
  4*(arc (2:ℝ)⁻¹ n+arc (3:ℝ)⁻¹ n)

theorem star_est (n):
    |polestar n - π| ≤ 16*drop_ n := by
  have A := arc_cost 2 n (by decide)
  have B := arc_cost 3 n (by decide)
  push_cast at A B
  unfold polestar
  rw [abs_le] at *
  obtain ⟨a,b⟩:= A
  obtain ⟨d,e⟩:= B
  constructor <;> linarith [Real.arctan_inv_2_add_arctan_inv_3]

theorem star_le {n} (x:4≤n) : |polestar n| ≤5 := by
  have z := drop_le x
  unfold drop_ at z
  norm_num1 at z
  have h : |polestar n| ≤ |polestar n -π|+|π| := by simpa using (abs_add_le (polestar n-π) π)
  rw [abs_of_pos Real.pi_pos] at h
  linarith [star_est n, Real.pi_lt_four]

end
end Star

end IntegerMultiplication
end Computability
end OAI
