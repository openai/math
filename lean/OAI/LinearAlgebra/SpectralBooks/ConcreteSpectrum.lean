import OAI.LinearAlgebra.SpectralBooks.SiteSpectrum
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Nonzero
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal

/-! # The compact spectrum of actual finite-party tensors -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped NNReal

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]

/-- The full diagonal indexed by the coefficient positions bounds the tensor class. -/
theorem exists_le_natCast (X : TensorClass.{v} I K) : ∃ n : ℕ, X ≤ n := by
  classical
  induction X using Quotient.inductionOn with
  | _ T =>
    refine ⟨Fintype.card (∀ i, T.Leg i), ?_⟩
    change ofRaw T ≤ (Fintype.card (∀ i, T.Leg i) : TensorClass.{v} I K)
    simpa only [ofRaw_diagonal_eq_natCast, Fintype.card_ulift, Fintype.card_fin] using
        (ofRaw_le_iff.mpr (T.restricts_diagonal I))

/-- The compactness assertion of the spectral comparison proposition with
the genuine tensor semiring and local restriction order. -/
theorem isCompact_spectrum :
    IsCompact (normalizedSpectrum (S := TensorClass.{v} I K) (· ≤ ·)) :=
  isCompact_normalizedSpectrum _ exists_le_natCast

theorem ofRaw_one_le_of_nonzero (X : Raw.{v} I K) (h : X.coeff ≠ 0) :
    1 ≤ ofRaw X :=
  X.one_restricts_of_nonzero h

/-- Every normalized spectral point evaluates a nonzero tensor positively. -/
theorem spectral_value_pos
    (φ : normalizedSpectrum (S := TensorClass.{v} I K) (· ≤ ·))
    {X : TensorClass.{v} I K} (h : X ≠ 0) : 0 < φ.val X := by
  have hu := φ.property.2.2.2.2 1 X (one_le_of_ne_zero h)
  rw [φ.property.2.1] at hu
  exact zero_lt_one.trans_le hu

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
