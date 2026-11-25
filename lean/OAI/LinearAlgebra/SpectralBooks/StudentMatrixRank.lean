import OAI.LinearAlgebra.SpectralBooks.BookRank
import OAI.LinearAlgebra.SpectralBooks.StudentBook

/-! # Matrix rank and the higher-dimensional book

The field enters through the normalized spectral evaluation on each placement
of the three wires. Multiplicativity evaluates the matrix multiplication tensor
and the flattenings give each individual load bound.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

section

open scoped NNReal Classical

variable (F : Type*) [Field F] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The individual loads in the finite Student theorem are bounded by the base-two
logarithm of asymptotic rank over the original field. -/
theorem matrix_load_le_log_asymptoticRank {x y z : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (i : Fin 3) :
    loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z) i ≤
      Real.logb 2 (asymptoticRank (matrixTensor F x y z)) := by
  have hlog {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
      (hprod : ((a*b : ℕ) : ℝ) ≤ asymptoticRank (matrixTensor F x y z)) :
      Real.logb 2 a + Real.logb 2 b ≤ Real.logb 2 (asymptoticRank (matrixTensor F x y z)) := by
    rw [← Real.logb_mul (by positivity : (a : ℝ) ≠ 0) (by positivity : (b : ℝ) ≠ 0)]
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    simpa using hprod
  have hh := matrix_flattening_le_asymptoticRank F hx hy hz
  push_cast at hh
  obtain ⟨h₁, h₂, h₃⟩ := (max_le_iff.mp hh).imp_right max_le_iff.mp
  fin_cases i
  · exact hlog hz hx (by simpa using h₁)
  · exact hlog hx hy (by simpa using h₂)
  · exact hlog hy hz (by simpa using h₃)

/-- The finite higher-dimensional theorem on a book whose diagonal has the flat
law and whose three tips admit a normalized spectral evaluation pricing each wire. -/
theorem matrix_student_bound_of_book {q : ℕ} (hE : Module.finrank ℝ E = q) (hq : 0 < q)
    (δ : Finset (Book E) → ℝ) (hmono : Monotone δ) (hsub : IntersectingSubmodular δ)
    (hflat : ∀ (e : Book.Lift E → Book E), Isometry e →
      ∀ (S : Finset (Book.Lift E)) (hS : S.Nonempty), δ (S.image e) = meanWidth S hS)
    (wires : ∀ (a : Fin 3 → ℝ≥0), (∀ i, 0 < a i) →
      let p := fun i ↦ bookPoint i (a i) (0 : E)
      PlacedWires F p (δ (Finset.univ.image p)))
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    let m := loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z)
    let L := Real.logb 2 (asymptoticRank (matrixTensor F x y z))
    (∀ i, m i ≤ L) ∧ StudentBound (q + 1) m L := by
  dsimp only
  have hlog (n : ℕ) (hn : 0 < n) := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hn : 1 ≤ (n : ℝ))
  have hm := loads_nonneg (hlog x hx) (hlog y hy) (hlog z hz)
  have hmL := matrix_load_le_log_asymptoticRank F hx hy hz
  refine ⟨hmL, student_bound_of_page_law hE hq δ hmono hsub hflat hm hmL ?_⟩
  intro a ha
  have hw := (wires a ha).wireSum_le hx hy hz
  simp only [book_dist_distinct_tips (by decide : (0 : Fin 3) ≠ 1),
    book_dist_distinct_tips (by decide : (1 : Fin 3) ≠ 2),
    book_dist_distinct_tips (by decide : (2 : Fin 3) ≠ 0)] at hw
  rw [mul_comm]
  refine le_trans (le_of_eq ?_) hw
  simp [Fin.sum_univ_three, loads]
  ring

end

end

end SpectralBooks
end LinearAlgebra
end OAI
