import OAI.LinearAlgebra.SpectralBooks.DualExponent
import OAI.LinearAlgebra.SpectralBooks.Flattening
import OAI.LinearAlgebra.SpectralBooks.GaussianTest

/-! # The Gaussian rectangular bound on arithmetic exponents -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Filter
open scoped Topology

section

/-- Pass the finite Gaussian tests to a polynomial exponent by applying them
at powers of two. The log of the multiplicative constant vanishes after
division by the dyadic scale. -/
theorem gaussianBound_of_polynomial_bound {w12 w23 w31 τ : ℝ}
    (hτ : ∀ i, loads w12 w23 w31 i ≤ τ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      GaussianBound (scaledLoads N w12 w23 w31) (Real.logb 2 (C * (N : ℝ) ^ (τ + ε)))) :
    GaussianBound (loads w12 w23 w31) τ := by
  by_cases hpos : ∃ i, 0 < loads w12 w23 w31 i
  swap
  · push Not at hpos
    simp [GaussianBound, hpos, not_lt.mpr]
  obtain ⟨i, hi⟩ := hpos
  have hτpos := hi.trans_le (hτ i)
  apply gaussianBound_of_tendsto hτpos.ne' (f := 𝓝[>] (0 : ℝ))
    (v := fun ε => τ + ε) (by simpa using (continuousWithinAt_id (s := Set.Ioi 0)
      (x := (0 : ℝ))).tendsto.const_add τ)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  obtain ⟨C, hC, hN⟩ := h ε hε'
  have hCpos := zero_lt_one.trans_le hC
  have hlog : 0 ≤ Real.logb 2 C := Real.logb_nonneg (by norm_num) hC
  have hu : 0 < τ + ε := add_pos hτpos hε'
  let p (k : ℕ) := Real.logb 2 C / k + (τ + ε)
  have hp : Tendsto p atTop (𝓝 (τ + ε)) := by
    have h0 := (tendsto_const_div_atTop_nhds_zero_nat (Real.logb 2 C)).add_const (τ + ε)
    simpa [p] using h0
  apply gaussianBound_of_tendsto hu.ne' hp
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have ht := hN (2 ^ k) (Nat.one_le_pow _ _ (by decide))
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_mul hCpos.ne' (by positivity),
    Real.logb_rpow_eq_mul_logb_of_pos (by positivity), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one] at ht
  have hp' : (k : ℝ) * p k = Real.logb 2 C + (τ + ε) * k := by dsimp [p]; field
  apply (gaussianBound_smul_iff (c := (k : ℝ)) hk').mp
  rw [hp']
  exact ht.lowerLoads (by positivity) (dyadic_load_le k w12 w23 w31)

section

variable {F : Type*} [Field F]
variable (hfinite : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
  GaussianBound (loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z))
    (Real.logb 2 (asymptoticRank (matrixTensor F x y z))))

include hfinite

/-- The Gaussian finite-format test implies the same test for the formal
arithmetic exponent at every triple of nonnegative real wire weights. -/
theorem formalOmega_gaussianBound {w12 w23 w31 : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) :
    GaussianBound (loads w12 w23 w31) (formalOmega F w12 w23 w31) := by
  apply gaussianBound_of_polynomial_bound (load_le_formalOmega F h12 h23 h31)
  intro ε hε
  obtain ⟨C, _, hC⟩ := (formalOmega_admissible F h12 h23 h31).rank_growth ε hε
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro N hN
  have hw (w : ℝ) := wireDimension_pos (N := N) (by omega) w
  let x := wireDimension N w12
  let y := wireDimension N w23
  let z := wireDimension N w31
  have hrank : 1 ≤ asymptoticRank (matrixTensor F x y z) := by
    refine le_trans ?_ (matrix_flattening_le_asymptoticRank F (hw w12) (hw w23) (hw w31))
    exact_mod_cast (Nat.succ_le_iff.mpr
      ((Nat.mul_pos (hw w31) (hw w12)).trans_le (le_max_left _ _)))
  apply (hfinite x y z (hw w12) (hw w23) (hw w31)).mono (Real.logb_nonneg (by norm_num) hrank)
  apply Real.logb_le_logb_of_le (by norm_num) (zero_lt_one.trans_le hrank)
  apply (asymptoticRank_le_tensorRank _).trans
  apply (hC N hN).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- In particular the actual square multiplication exponent obeys the normal
quantile lower bound when the finite Gaussian branch holds. -/
theorem formalOmega_gaussian_square_lower_bound :
    2 * Real.exp (stdNormalQuantile (2 / 3) ^ 2 / 2) ≤ formalOmega F 1 1 1 := by
  have h1 : (0 : ℝ) ≤ 1 := zero_le_one
  apply gaussian_square_lower_bound
  · have he := load_le_formalOmega F h1 h1 h1 0
    norm_num [loads] at he
    exact he
  · have hs : loads 1 1 1 = fun _ : Fin 3 => (2 : ℝ) := by
      ext i
      fin_cases i <;> norm_num [loads]
    simpa only [hs] using formalOmega_gaussianBound hfinite h1 h1 h1

/-- Every admissible dual shape satisfies the smaller quantile upper bound. -/
theorem formalOmega_gaussian_dual_weight_bound {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (htwo : formalOmega F 1 1 t = 2) :
    t ≤ 2 * Real.exp (-(stdNormalQuantile (3 / 4) ^ 2) / 2) - 1 := by
  apply gaussian_dual_weight_bound ht ht'
  have hs : loads 1 1 t = ![1 + t, 2, 1 + t] := by
    ext i
    fin_cases i <;> norm_num [loads, add_comm]
  simpa only [hs, htwo] using formalOmega_gaussianBound hfinite zero_le_one zero_le_one ht

/-- The full dual-exponent consequence in the Gaussian corollary. -/
theorem formalAlpha_gaussian_upper_bound :
    formalAlpha F ≤ 2 * Real.exp (-(stdNormalQuantile (3 / 4) ^ 2) / 2) - 1 :=
  formalAlpha_le fun _ ht => formalOmega_gaussian_dual_weight_bound hfinite ht.1 ht.2

end

end

end SpectralBooks
end LinearAlgebra
end OAI
