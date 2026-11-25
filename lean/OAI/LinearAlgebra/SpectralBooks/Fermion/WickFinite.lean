import OAI.LinearAlgebra.SpectralBooks.Fermion.Fock
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickContraction

/-! # Finite exterior-algebra matrices for the Laurent fields -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion

/-- Creation part of a differentiated field with modes below `N`. -/
def creationField (N : ℕ) (f : FieldLabel) :
    Matrix (FockState N) (FockState N) (LaurentPolynomial ℤ) :=
  ∑ r : Fin N, creationCoeff f r.val • creation (LaurentPolynomial ℤ) r

/-- Annihilation part of a differentiated field with modes below `N`. -/
def annihilationField (N : ℕ) (f : FieldLabel) :
    Matrix (FockState N) (FockState N) (LaurentPolynomial ℤ) :=
  ∑ r : Fin N, annihilationCoeff f r.val • annihilation (LaurentPolynomial ℤ) r

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
