import OAI.LinearAlgebra.SpectralBooks.FormalRecursion
import OAI.LinearAlgebra.SpectralBooks.AbsoluteTensorRank
import OAI.LinearAlgebra.SpectralBooks.MatrixPower

/-! # Tensor powers and the square arithmetic exponent -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation Filter
open scoped Topology

noncomputable section

/-- Polynomial rank growth at unit wire weights bounds the asymptotic rank of
each fixed square format, after taking roots along tensor powers. -/
theorem square_asymptoticRank_le_of_rank_growth (F : Type*) [Field F] {n : ℕ} (hn : 0 < n)
    {ω : ℝ} (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (tensorRank (matrixTensor F (wireDimension N 1) (wireDimension N 1) (wireDimension N 1)) : ℝ)
        ≤ C * (N : ℝ) ^ (ω + ε)) :
    asymptoticRank (matrixTensor F n n n) ≤ (n : ℝ) ^ ω := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hcont : Continuous fun ε : ℝ => (n : ℝ) ^ (ω + ε) :=
    (Real.continuous_const_rpow hn').comp (continuous_const.add continuous_id)
  have hlim : Tendsto (fun ε : ℝ => (n : ℝ) ^ (ω + ε)) (𝓝[>] 0) (𝓝 ((n : ℝ) ^ ω)) := by
    simpa using (hcont.continuousAt (x := 0) |>.continuousWithinAt (s := Set.Ioi 0)).tendsto
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨C, hC, hbound⟩ := hgrowth ε hε
  let r := (n : ℝ) ^ (ω + ε)
  have wd (N : ℕ) : wireDimension N 1 = N := by simp [wireDimension]
  have hr : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hroot : Tendsto (fun k : ℕ => C ^ ((k : ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero, Function.comp_def] using
      (Real.continuousAt_const_rpow (a := C) (b := 0) hC.ne').tendsto.comp
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  apply le_of_tendsto_of_tendsto (tendsto_tensorRank_power_root _)
    (show Tendsto (fun k : ℕ => C ^ ((k : ℝ)⁻¹) * r) atTop (𝓝 r) by simpa using hroot.mul_const r)
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with k hk
  have hg : (tensorRank (Tensor.power (matrixTensor F n n n) k) : ℝ) ≤ C * r ^ k := by
    rw [tensorRank_matrixTensor_power]
    have hb := hbound (n ^ k) (Nat.one_le_pow _ _ hn)
    rw [wd] at hb
    simpa only [Nat.cast_pow,
      ← Real.rpow_natCast_mul (Nat.cast_nonneg n), mul_comm (k : ℝ), Real.rpow_mul_natCast
      (Nat.cast_nonneg n)] using hb
  calc
    _ ≤ (C * r ^ k) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hg (by positivity)
    _ = _ := by rw [Real.mul_rpow hC.le (pow_nonneg hr _), Real.pow_rpow_inv_natCast hr hk]

/-- Formal square circuits bound asymptotic rank over their ground field. -/
theorem square_asymptoticRank_le_rpow_formalOmega (F : Type*) [Field F] {n : ℕ} (hn : 0 < n) :
    asymptoticRank (matrixTensor F n n n) ≤ (n : ℝ) ^ formalOmega F 1 1 1 :=
  square_asymptoticRank_le_of_rank_growth F hn
    (formalOmega_admissible F (by norm_num) (by norm_num) (by norm_num)).rank_growth

/-- A uniform bound on the exponent from each finite square rank formula also holds
for the asymptotic rank, by applying it at each power of the fixed order. -/
theorem rpow_formalOmega_le_asymptoticRank (F : Type*) [Field F] {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ formalOmega F 1 1 1 ≤ asymptoticRank (matrixTensor F n n n) := by
  apply le_ciInf
  intro k
  rw [tensorRank_matrixTensor_power]
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (show 0 < (k : ℝ) + 1 by positivity)).mpr
  rw [← Nat.cast_succ, Real.rpow_natCast, Real.rpow_pow_comm (Nat.cast_nonneg n), ← Nat.cast_pow]
  apply rpow_formalOmega_le_tensorRank
  exact hn.trans (le_self_pow (by omega) (by omega))

/-- At every square order at least two, asymptotic rank equals the order
raised to the formal arithmetic exponent over the same field. -/
theorem square_asymptoticRank_eq_rpow_formalOmega (F : Type*) [Field F] {n : ℕ} (hn : 2 ≤ n) :
    asymptoticRank (matrixTensor F n n n) = (n : ℝ) ^ formalOmega F 1 1 1 :=
  le_antisymm (square_asymptoticRank_le_rpow_formalOmega F (by omega))
    (rpow_formalOmega_le_asymptoticRank F hn)

/-- The square arithmetic exponent, defined by formal identities, depends only
on the characteristic of the field. -/
theorem formalOmega_square_eq_of_ringChar_eq (F E : Type*) [Field F] [Field E]
    (hchar : ringChar F = ringChar E) : formalOmega F 1 1 1 = formalOmega E 1 1 1 := by
  have h := asymptoticRank_matrixTensor_eq_of_ringChar_eq F E hchar 2 2 2
  rw [square_asymptoticRank_eq_rpow_formalOmega F (by decide),
      square_asymptoticRank_eq_rpow_formalOmega E (by decide)] at h
  exact (Real.rpow_right_inj (by norm_num) (by norm_num)).mp h

/-- The finite asymptotic-rank radical inequality at order two alone would force
the superquadratic arithmetic lower bound over the same field. -/
theorem formalOmega_square_lower_bound_of_order_two (F : Type*) [Field F]
    (h : RadicalTest (fun _ => 2) (Real.logb 2 (asymptoticRank (matrixTensor F 2 2 2)))) :
    3 / Real.sqrt 2 ≤ formalOmega F 1 1 1 := by
  rw [square_asymptoticRank_eq_rpow_formalOmega F (by decide), Nat.cast_ofNat,
    Real.logb_rpow (by norm_num) (by norm_num)] at h
  exact square_lower_bound h

end

end SpectralBooks
end LinearAlgebra
end OAI
