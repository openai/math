import OAI.LinearAlgebra.SpectralBooks.StudentTestFromFlat
import OAI.Hierarchy.MatrixFieldTransfer
import OAI.Hierarchy.FlatPrices

namespace OAI
/-! # Rectangular matrix multiplication from unbounded spectral flats

Section 3 of the arithmetic formulas paper uses finite-dimensional spectral flats to obtain the
Student inequalities along dimensions tending to infinity. The square and dual constants below
are exact normal quantiles.
-/

namespace Hierarchy

open MatrixMultiplication LinearAlgebra.SpectralBooks Filter

/-- Arbitrarily large Euclidean spaces carry compatible spectral placement prices over every
positive-characteristic prime field. Only this cofinal form of the paper's flats theorem is
needed for the matrix inequalities. -/
def UnboundedPrimeFieldFlats : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ᶠ D : ℕ in atTop,
    HasSpectralFlat (ZMod p) D

/-- All positive dimensions from the paper's flats theorem give the cofinal input. -/
theorem UnboundedPrimeFieldFlats.of_all
    (flats : ∀ (p : ℕ) [Fact p.Prime], ∀ D : ℕ, 0 < D → HasSpectralFlat (ZMod p) D) :
    UnboundedPrimeFieldFlats := by
  intro p _
  exact ((eventually_gt_atTop (0 : ℕ)).mono (flats p)).frequently

/-- Passing from finite-dimensional Student tests to the normal test uses only a cofinal family
of spectral Euclidean flats over the given field. -/
theorem gaussianMatrixTest_of_unbounded_flats (K : Type) [Field K]
    (flats : ∃ᶠ D : ℕ in atTop,
      HasSpectralFlat K D) :
    GaussianMatrixTest K := by
  apply gaussianMatrixTest_of_unbounded_student
  exact (flats.and_eventually (eventually_ge_atTop 2)).mono fun _ h =>
    studentMatrixTest_of_spectral_flat K (fun _ _ _ Q hg => Q.catZero hg) h.2 h.1

/-- The two inequalities in the finite-format Gaussian rank test. -/
def GaussianRankInequality (m : Fin 3 → ℝ) (L : ℝ) : Prop :=
  (∀ i, m i ≤ L) ∧ GaussianBound m L

/-- The complete rectangular rank theorem for asymptotic, geometric border and ordinary tensor
rank, including formats with vanishing logarithmic loads. -/
theorem rectangular_rank_inequalities (F : Type*) [Field F] (test : GaussianMatrixTest F)
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    let m := loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z)
    let M := matrixTensor F x y z
    GaussianRankInequality m (Real.logb 2 (asymptoticRank M)) ∧
      GaussianRankInequality m (Real.logb 2 (geometricBorderRank M)) ∧
      GaussianRankInequality m (Real.logb 2 (tensorRank M)) := by
  intro m M
  have load := matrix_load_le_log_asymptoticRank F hx hy hz
  have normal := test x y z hx hy hz
  have one : 1 ≤ asymptoticRank M := by
    refine le_trans ?_ (matrix_flattening_le_asymptoticRank F hx hy hz)
    exact_mod_cast (Nat.succ_le_iff.mpr ((Nat.mul_pos hz hx).trans_le (le_max_left _ _)))
  have extend (U : ℝ) (h : asymptoticRank M ≤ U) : GaussianRankInequality m (Real.logb 2 U) := by
    have le := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (zero_lt_one.trans_le one) h
    exact ⟨fun i => (load i).trans le, normal.mono (Real.logb_nonneg (by norm_num) one) le⟩
  exact ⟨⟨load, normal⟩, extend _ (asymptoticRank_le_geometricBorderRank M),
    extend _ (asymptoticRank_le_tensorRank M)⟩

/-- The same Gaussian test at every nonnegative rectangular exponent triple, followed by its
exact square lower and dual upper bounds. -/
theorem matrix_exponent_inequalities (F : Type*) [Field F] (test : GaussianMatrixTest F) :
    (∀ {a b c : ℝ}, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      GaussianRankInequality (loads a b c) (formalOmega F a b c)) ∧
    2 * Real.exp (stdNormalQuantile (2 / 3) ^ 2 / 2) ≤ formalOmega F 1 1 1 ∧
    formalAlpha F ≤ 2 * Real.exp (-(stdNormalQuantile (3 / 4) ^ 2) / 2) - 1 :=
  ⟨fun ha hb hc => ⟨load_le_formalOmega F ha hb hc, formalOmega_gaussianBound test ha hb hc⟩,
    formalOmega_gaussian_square_lower_bound test, formalAlpha_gaussian_upper_bound test⟩

/-- The Gaussian finite-format inequality over every field follows from the geometric input
over the positive-characteristic prime fields. This includes fields of characteristic zero. -/
theorem gaussianMatrixTest_of_prime_flats (flats : UnboundedPrimeFieldFlats)
    (F : Type*) [Field F] : GaussianMatrixTest F :=
  gaussianMatrixTest_of_prime_fields
    (fun p _ => gaussianMatrixTest_of_unbounded_flats (ZMod p) (flats p)) F

/-- The two exact exponent bounds of the paper over an arbitrary ground field. -/
theorem matrix_exponents_of_prime_flats (flats : UnboundedPrimeFieldFlats)
    (F : Type*) [Field F] :
    2 * Real.exp (stdNormalQuantile (2 / 3) ^ 2 / 2) ≤ formalOmega F 1 1 1 ∧
    formalAlpha F ≤ 2 * Real.exp (-(stdNormalQuantile (3 / 4) ^ 2) / 2) - 1 :=
  (matrix_exponent_inequalities F (gaussianMatrixTest_of_prime_flats flats F)).2


end Hierarchy

end OAI
