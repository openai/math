import OAI.LinearAlgebra.SpectralBooks.BookSpineBall
import OAI.LinearAlgebra.SpectralBooks.Dimension
import OAI.LinearAlgebra.SpectralBooks.SpineRadial

/-! # The finite Student test in a spectral book

The Gaussian diagonal law on each Euclidean flat of the book bounds the
price denominator of three tips. A bound on their normalized tensor price
then yields the Student test at the incident loads.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open scoped Classical NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The finite Student inequality from the flat diagonal law and the spectral
upper bound on the matrix multiplication price evaluated on the three tips. -/
theorem student_bound_of_page_law {q : ℕ} (hE : Module.finrank ℝ E = q) (hq : 0 < q)
    (δ : Finset (Book E) → ℝ) (hmono : Monotone δ) (hsub : IntersectingSubmodular δ)
    (hflat : ∀ (e : Book.Lift E → Book E), Isometry e →
      ∀ (S : Finset (Book.Lift E)) (hS : S.Nonempty), δ (S.image e) = meanWidth S hS)
    {L : ℝ} {m : Fin 3 → ℝ} (hm : ∀ i, 0 ≤ m i) (hmL : ∀ i, m i ≤ L)
    (hprice : ∀ a : Fin 3 → ℝ≥0, (∀ i, 0 < a i) →
      ∑ i, (a i : ℝ) * m i ≤ L * δ (Finset.univ.image (fun i ↦ bookPoint i (a i) (0 : E)))) :
    StudentBound (q + 1) m L := by
  have hL := (hm 0).trans (hmL 0)
  have hp (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
      ∑ i, a i * m i ≤ L * Real.sqrt (2 * Real.pi) * spineBallExpectation E a := by
    let b : Fin 3 → ℝ≥0 := fun i ↦ ⟨a i, (ha i).le⟩
    have hb := hprice b (fun i ↦ ha i)
    refine hb.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (book_tips_le_spineBall δ hmono hsub hflat b) hL
  simpa only [StudentBound, Nat.cast_add_one, add_sub_cancel_right] using
    student_bound_of_spineBall hE hq hL hm hmL hp

end

end

end SpectralBooks
end LinearAlgebra
end OAI
