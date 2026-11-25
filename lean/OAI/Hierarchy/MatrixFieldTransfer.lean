import OAI.LinearAlgebra.SpectralBooks.CharacteristicAlternative
import OAI.LinearAlgebra.SpectralBooks.RankLimit
import OAI.ThreeFlat.FiniteFieldReduction

namespace OAI
/-! # Transfer of the rectangular Gaussian rank test to every field

For each tensor power, a finite residue field preserves an optimal rank decomposition.
The field may vary with the power. The logarithms of the rank roots converge to the
logarithm of asymptotic rank over the original field.
-/

namespace Hierarchy

open Filter MatrixMultiplication.Foundation LinearAlgebra.SpectralBooks
open ThreeFlat
open scoped Topology

private theorem matrix_rank_one_le (F : Type*) [Field F] {x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 ≤ asymptoticRank (matrixTensor F x y z) := by
  refine le_trans ?_ (matrix_flattening_le_asymptoticRank F hx hy hz)
  exact_mod_cast (Nat.succ_le_iff.mpr ((Nat.mul_pos hz hx).trans_le (le_max_left _ _)))

/-- The Gaussian matrix test over all finite prime fields gives the test in every
rectangular format over any field, including fields of characteristic zero. -/
theorem gaussianMatrixTest_of_prime_fields
    (pTest : ∀ (p : ℕ) [Fact p.Prime], GaussianMatrixTest (ZMod p))
    (F : Type*) [Field F] : GaussianMatrixTest F := by
  intro x y z hx hy hz
  let m := loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z)
  change GaussianBound m _
  by_cases hpos : ∃ i, 0 < m i
  swap
  · push Not at hpos
    simp [GaussianBound, hpos, not_lt.mpr]
  obtain ⟨i, hi⟩ := hpos
  have hlog := hi.trans_le (matrix_load_le_log_asymptoticRank F hx hy hz i)
  apply gaussianBound_of_tendsto hlog.ne'
    ((tendsto_tensorRank_power_root (matrixTensor F x y z)).logb
      (zero_lt_one.trans_le (matrix_rank_one_le F hx hy hz)).ne')
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  cases n with
  | zero => omega
  | succ k =>
    obtain ⟨E, fE, hE, hr⟩ :=
      exists_finite_field_matrixRank_le F (x ^ (k+1)) (y ^ (k+1)) (z ^ (k+1))
    let p := ringChar E
    let : Fact p.Prime := ⟨CharP.char_is_prime E p⟩
    have htest := (gaussianMatrixTest_iff_of_charP (ZMod p) E p).mp (pTest p)
    have hone := matrix_rank_one_le E hx hy hz
    apply (htest x y z hx hy hz).mono (Real.logb_nonneg (by norm_num) hone)
    apply Real.logb_le_logb_of_le (by norm_num) (zero_lt_one.trans_le hone)
    apply (ciInf_le (f := fun j : ℕ ↦ (tensorRank
        (Tensor.power (matrixTensor E x y z) (j+1)) : ℝ) ^ ((j+1 : ℝ)⁻¹))
        ⟨0, by rintro _ ⟨j, rfl⟩; positivity⟩ k).trans
    simp only [tensorRank_matrixTensor_power, Nat.cast_succ]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hr) (by positivity)

end Hierarchy

end OAI
