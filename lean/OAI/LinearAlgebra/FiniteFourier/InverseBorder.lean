import OAI.LinearAlgebra.FiniteFourier.FeedbackBorderReindex
import OAI.LinearAlgebra.FiniteFourier.InverseComplexity

/-! # Forward and inverse Fourier transforms in geometric border -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- The forward and inverse character transforms belong to exactly the same
geometric border feedback-size sublevels. -/
theorem geometricBorderAtMost_inverseFourierMatrix_iff
    (G K : Type*) [AddCommGroup G] [Fintype G] [Field K] (h : Admissible G K) (S : ℕ) :
    GeometricBorderAtMost (inverseFourierMatrix G K) S ↔
      GeometricBorderAtMost (fourierMatrix G K) S := by
  obtain ⟨R, E, he⟩ := exists_reindex_inverseFourierMatrix G K h
  rw [he, geometricBorderAtMost_smul_iff _ _ (inv_ne_zero h.1), geometricBorderAtMost_reindex_iff]

end FiniteFourier
end LinearAlgebra
end OAI
