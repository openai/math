import OAI.LinearAlgebra.SpectralBooks.Fermion.WickFinite
import OAI.LinearAlgebra.SpectralBooks.Fermion.CARWeighted
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickSkew

/-! # Wick expansion of the truncated differentiated fields -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion

open scoped BigOperators

theorem creationField_anticommute (N : ℕ) (f g : FieldLabel) :
    creationField N f * creationField N g + creationField N g * creationField N f = 0 :=
  weighted_same_modes _ (creation_mul_creation (LaurentPolynomial ℤ)) _ _

theorem annihilationField_anticommute (N : ℕ) (f g : FieldLabel) :
    annihilationField N f * annihilationField N g + annihilationField N g * annihilationField N f = 0 :=
  weighted_same_modes _ (annihilation_mul_annihilation (LaurentPolynomial ℤ)) _ _

theorem annihilationField_creationField (N : ℕ) (f g : FieldLabel) :
    annihilationField N f * creationField N g + creationField N g * annihilationField N f =
      algebraMap (LaurentPolynomial ℤ) _ (contractionPolynomial N f g) :=
  weighted_mixed_modes _ _ (annihilation_mul_creation (LaurentPolynomial ℤ)) _ _

/-- Wick expansion for the actual exterior-algebra operators at finite cutoff. -/
theorem finite_normal_mul_normal (N : ℕ) (l r : List FieldLabel) :
    normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N) l *
      normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N) r =
      ∑ p : Matching l r, p.weight (contractionPolynomial N) •
        normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N) p.residual :=
  normal_mul_normal _ _ _ (annihilationField_creationField N) (annihilationField_anticommute N) l r

/-- Exchanging two consecutive normal subwords gives the parity of the block exchange. -/
theorem finite_normal_append_swap (N : ℕ) (l r : List FieldLabel) :
    normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N) (l ++ r) =
      (-1 : LaurentPolynomial ℤ) ^ (l.length * r.length) •
        normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N) (r ++ l) :=
  normal_append_swap _ _ _ (creationField_anticommute N) (annihilationField_anticommute N) l r

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
