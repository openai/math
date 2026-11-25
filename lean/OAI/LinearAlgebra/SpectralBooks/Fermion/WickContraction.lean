import OAI.LinearAlgebra.SpectralBooks.Fermion.WickPolynomial

/-! # Scalar contractions between finite fermionic fields -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

/-- The scalar obtained when the annihilation part of one field crosses the
creation part of the other, with the modes truncated at `N`. -/
noncomputable def contractionPolynomial (N : ℕ) (f g : FieldLabel) : LaurentPolynomial ℤ :=
  ∑ r : Fin N, annihilationCoeff f r.val * creationCoeff g r.val

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
