import OAI.LinearAlgebra.SpectralBooks.Dimension
import OAI.LinearAlgebra.SpectralBooks.GaussianExponent
import OAI.LinearAlgebra.SpectralBooks.DivisionExponent
import OAI.LinearAlgebra.SpectralBooks.SignedWitnessBorder
import OAI.LinearAlgebra.SpectralBooks.AbsoluteTensorRank
import OAI.LinearAlgebra.SpectralBooks.ProfileShortening
import OAI.LinearAlgebra.SpectralBooks.SpectralAxisComparison
import OAI.LinearAlgebra.SpectralBooks.SpectralCrossingShortening
import OAI.LinearAlgebra.SpectralBooks.StudentMatrixRank

/-!
# The characteristic-wise alternative

The matrix branch quantifies over every finite format and the circuit branch uses the degree-`n`
component of the explicit signed-path polynomial. The exponent in the circuit branch is chosen
before the field. `CharacteristicAlternative` is the statement of the theorem in the manuscript.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Filter

/-- The Gaussian inequality in every finite rectangular format over `F`. -/
def GaussianMatrixTest (F : Type*) [Field F] : Prop :=
  ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
    GaussianBound (loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z))
      (Real.logb 2 (asymptoticRank (matrixTensor F x y z)))

/-- The Student inequality in dimension `D` over `F`. -/
def StudentMatrixTest (F : Type*) [Field F] (D : ℕ) : Prop :=
  ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
    StudentBound D (loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z))
      (Real.logb 2 (asymptoticRank (matrixTensor F x y z)))

universe u

/-- The matrix multiplication or circuit hardness alternative in characteristic `p`. -/
def CharacteristicAlternative (p : ℕ) : Prop :=
  (∀ (F : Type u) [Field F] [CharP F p], GaussianMatrixTest F ∧
    2 * Real.exp (stdNormalQuantile (2 / 3) ^ 2 / 2) ≤ divisionOmega F 1 1 1) ∨
  ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Type u) [Field F] [CharP F p], SignedWitnessHardness F ε

/-- Unbounded dimensions satisfying the finite Student tests give the finite Gaussian branch. -/
theorem gaussianMatrixTest_of_unbounded_student (F : Type*) [Field F]
    (h : ∃ᶠ D : ℕ in atTop, StudentMatrixTest F D) : GaussianMatrixTest F := by
  intro x y z hx hy hz
  apply gaussianBound_of_frequently_studentBound (matrix_load_le_log_asymptoticRank F hx hy hz)
  exact h.mono fun _ hD ↦ hD x y z hx hy hz

/-- One algebraic closure of a prime field suffices for the matrix branch as well. -/
theorem gaussianMatrixTest_iff_of_charP (F G : Type*) [Field F] [Field G] (p : ℕ)
    [CharP F p] [CharP G p] : GaussianMatrixTest F ↔ GaussianMatrixTest G := by
  simp only [GaussianMatrixTest, matrix_asymptoticRank_eq_of_charP F G p]

universe v

/-- The price-preserving realization of the marked sites used from the CAT(0) extension theorem.
Every nonzero tensor on the old sites retains its normalized log price. -/
def HasSpectralAxisExtensions (F : Type*) [Field F] (D : ℕ) : Prop :=
  ∀ φ : Crossing.AxisSpectrum F D, ∃ (X : Type v) (metric : MetricSpace X),
    letI := metric
    ∃ (_ : HyperbolicObstruction.CATZero X) (P : SpectralPlacementPrices F X)
        (y : Crossing.AxisSite D → X),
      ∀ T : SiteTensor.Raw.{0} (Crossing.AxisSite D) F, T.coeff ≠ 0 →
        P.price T y = Real.logb 2 (φ.val (SiteTensor.ofRaw T) : ℝ)

/-- The missing-flat branch produces a genuine finite fixed-format shortening. -/
theorem shortenedCrossing_of_no_flat (F : Type*) [Field F] {D : ℕ} (hD : 2 ≤ D)
    (extend : HasSpectralAxisExtensions.{v} F D)
    (missing : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin D)))) :
    ∃ m : ℕ, 0 < m ∧ Crossing.ShortenedCrossing F D m := by
  apply Crossing.exists_shortenedCrossing_of_spectral_gap hD
  intro φ
  obtain ⟨X, metric, hcat, P, y, hold⟩ := extend φ
  let := metric
  exact Crossing.exists_strict_wire_of_missing_flat (by omega) φ P hcat y hold missing

/-- Reduction of the characteristic-wise theorem to the per-dimension geometric test and the
companion paper's border stretch theorem for profiled shortenings. Both resulting branches use exactly the
ranks, field quantifiers, and exponents from the manuscript. -/
theorem characteristicAlternative_of_student_or_shortened (k : Type*) [Field k] (p : ℕ)
    [CharP k p]
    (dimensionAlternative : ∀ D : ℕ, 2 ≤ D → StudentMatrixTest k D ∨
      ∃ m : ℕ, 0 < m ∧ Crossing.ShortenedCrossing k D m)
    (borderStretch : ∀ D : ℕ, 2 ≤ D → Crossing.HasProfileShortening k D →
      ∃ ε : ℝ, 0 < ε ∧ SignedWitnessHardness k ε) : CharacteristicAlternative.{u} p := by
  by_cases hs : ∃ D m : ℕ, 2 ≤ D ∧ 0 < m ∧ Crossing.ShortenedCrossing k D m
  · obtain ⟨D, m, hD, hm, hs⟩ := hs
    obtain ⟨ε, hε, hard⟩ := borderStretch D hD (hs.hasProfileShortening hD hm)
    exact Or.inr ⟨ε, hε, fun F _ _ ↦ (signedWitnessHardness_iff_of_charP k F p ε).mp hard⟩
  · left
    have hstudent : ∀ᶠ D : ℕ in atTop, StudentMatrixTest k D := by
      filter_upwards [eventually_ge_atTop 2] with D hD
      obtain h | ⟨m, hm, h⟩ := dimensionAlternative D hD
      · exact h
      · exact False.elim (hs ⟨D, m, hD, hm, h⟩)
    intro F _ _
    have hgauss := (gaussianMatrixTest_iff_of_charP k F p).mp
      (gaussianMatrixTest_of_unbounded_student k hstudent.frequently)
    exact ⟨hgauss, by rw [divisionOmega_square_eq_formalOmega]; exact formalOmega_gaussian_square_lower_bound hgauss⟩

/-- With price-preserving extensions, the higher-flat rank theorem and the border stretch theorem
suffice for the full characteristic-wise alternative. In the manuscript `k` is the algebraic
closure of the prime field in characteristic `p`. -/
theorem characteristicAlternative_of_spectral_extensions (k : Type*) [Field k] (p : ℕ)
    [CharP k p] (extend : ∀ D : ℕ, 2 ≤ D → HasSpectralAxisExtensions.{v} k D)
    (flatTest : ∀ D : ℕ, 2 ≤ D → Nonempty (SpectralPlacementPrices k (EuclideanSpace ℝ (Fin D))) →
      StudentMatrixTest k D)
    (borderStretch : ∀ D : ℕ, 2 ≤ D → Crossing.HasProfileShortening k D →
      ∃ ε : ℝ, 0 < ε ∧ SignedWitnessHardness k ε) : CharacteristicAlternative.{u} p := by
  apply characteristicAlternative_of_student_or_shortened k p _ borderStretch
  intro D hD
  by_cases h : Nonempty (SpectralPlacementPrices k (EuclideanSpace ℝ (Fin D)))
  · exact Or.inl (flatTest D hD h)
  · exact Or.inr (shortenedCrossing_of_no_flat k hD (extend D hD) h)

end SpectralBooks
end LinearAlgebra
end OAI
