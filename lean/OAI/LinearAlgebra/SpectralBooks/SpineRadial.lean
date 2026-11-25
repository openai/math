import OAI.LinearAlgebra.SpectralBooks.SpineBall
import OAI.LinearAlgebra.SpectralBooks.GaussianRadiusLaw
import OAI.LinearAlgebra.SpectralBooks.StudentHeight

/-! # The Student test for a Gaussian spine

The product integral for each tip separates into an expectation over the
spine radius and one over the independent normal page coordinate.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι]

/-- Express the spine-ball cost in terms of the chi mean and the radial hinge gains. -/
theorem spineBallExpectation_eq_radial {q : ℕ} (hE : Module.finrank ℝ E = q)
    (hq : 0 < q) (a : ι → ℝ) :
    spineBallExpectation E a = chiMean q + ∑ i, spineHinge q (a i) := by
  subst q
  have hr := integral_stdGaussian_norm_eq_chi_finrank E hq
  have hn : Integrable (fun w : E × ℝ ↦ ‖w.1‖) (spineGaussian E) :=
    (IsGaussian.integrable_id (μ := stdGaussian E)).norm.comp_fst _
  have hz (i : ι) : Integrable (fun w : E × ℝ ↦ a i * w.2) (spineGaussian E) :=
    ((IsGaussian.integrable_id (μ := gaussianReal 0 1)).comp_snd _).const_mul (a i)
  unfold spineBallExpectation
  congr 1
  · rw [integral_fun_fst, probReal_univ, one_smul]
    exact (hr (fun h ↦ h)).trans (by simpa [mul_comm] using integral_mul_chiDensity hq)
  · apply Finset.sum_congr rfl
    intro i _
    have hi : Integrable (fun w : E × ℝ ↦ max (a i * w.2 - ‖w.1‖) 0) (spineGaussian E) :=
      ((hz i).sub hn).sup (integrable_const 0)
    rw [integral_prod _ hi]
    exact hr (fun h ↦ ∫ z : ℝ, max (a i * z - h) 0 ∂gaussianReal 0 1)

/-- Equation `eq:student-bound` follows from the Gaussian book price inequality in
any spine of the specified positive dimension. -/
theorem student_bound_of_spineBall {q : ℕ} (hE : Module.finrank ℝ E = q) (hq : 0 < q)
    {L : ℝ} (hL : 0 ≤ L) {m : ι → ℝ} (hm : ∀ i, 0 ≤ m i) (hmL : ∀ i, m i ≤ L)
    (hprice : ∀ a : ι → ℝ, (∀ i, 0 < a i) →
      ∑ i, a i * m i ≤ L * Real.sqrt (2 * Real.pi) * spineBallExpectation E a) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < m i),
      studentTail (q + 1) (Real.sqrt (((q : ℝ) + 1) * ((L / m i) ^ (2 / (q : ℝ)) - 1))) ≤ 1 := by
  apply student_bound_of_spine_price hq hL hm hmL
  simpa only [spineBallExpectation_eq_radial hE hq] using hprice

end

end SpectralBooks
end LinearAlgebra
end OAI
