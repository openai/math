import OAI.LinearAlgebra.FiniteFourier.FeedbackBorderReindex
import OAI.LinearAlgebra.FiniteFourier.Transform
import Mathlib.Algebra.Group.Shrink

/-! # Transport of a finite Fourier problem along a group isomorphism -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [Field K]

/-- Reindex the characters by precomposing with the inverse group isomorphism. -/
def characterGroupEquiv (e : G ≃+ H) : Character G K ≃ Character H K :=
  (AddEquiv.toMultiplicative e).monoidHomCongrLeftEquiv

/-- Reindexing both the characters and the arguments transports the whole character table. -/
theorem reindex_fourierMatrix (e : G ≃+ H) :
    Matrix.reindex (characterGroupEquiv (K := K) e) e.toEquiv (fourierMatrix G K) =
      fourierMatrix H K := by
  ext χ h
  change (χ (Multiplicative.ofAdd (e (e.symm h))) : K) = _
  rw [e.apply_symm_apply]
  rfl

variable [Fintype G] [Fintype H]

/-- Both the group exponent and the order defining admissibility are isomorphism invariant. -/
theorem Admissible.of_groupEquiv (h : Admissible G K) (e : G ≃+ H) : Admissible H K := by
  rwa [Admissible, ← Fintype.card_congr e.toEquiv, ← AddMonoid.exponent_eq_of_addEquiv e]

omit [Fintype G] [Fintype H] in
/-- Geometric border feedback complexity of the Fourier matrix is independent of its
chosen presentation as a finite group. -/
theorem border_fourierMatrix_of_groupEquiv (e : G ≃+ H) {S : ℕ}
    (h : GeometricBorderAtMost (fourierMatrix G K) S) :
    GeometricBorderAtMost (fourierMatrix H K) S := by
  rw [← reindex_fourierMatrix (K := K) e]
  exact h.reindex _ _

end FiniteFourier
end LinearAlgebra
end OAI
