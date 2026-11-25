import OAI.LinearAlgebra.SpectralBooks.TensorFiniteDescent
import OAI.LinearAlgebra.SpectralBooks.TensorRestrictionSpecialize

/-! # Spectral comparisons of ground tensors after any scalar extension -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor

universe v
variable {I K L : Type*} [Fintype I] [Nonempty I] [Field K] [Field L] [Algebra K L]

/-- Every ground spectral point is monotone for comparisons of ground tensors
proved over any extension field. The finitely many defining equations specialize
to an algebraic closure and then descend, up to a fixed factor, to the ground
field on all powers. -/
theorem spectral_le_of_baseChange
    (φ : normalizedSpectrum (S := TensorClass.{v} I K) (· ≤ ·))
    {X Y : TensorClass.{v} I K}
    (h : mapScalars (algebraMap K L) X ≤ mapScalars (algebraMap K L) Y) :
    φ.val X ≤ φ.val Y := by
  induction X using Quotient.inductionOn with | _ X
  induction Y using Quotient.inductionOn with | _ Y
  obtain ⟨S, hS, hxy⟩ := Raw.exists_finite_restriction_of_mapScalars (X := X) (Y := Y) h
  exact spectral_le_of_finite_baseChange (L := S) φ hxy

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
