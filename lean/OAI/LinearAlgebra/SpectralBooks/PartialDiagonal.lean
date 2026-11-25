import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct
import OAI.LinearAlgebra.SpectralBooks.TensorSemiring
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.DiagonalRaw
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.DiagonalEmbedding
import OAI.LinearAlgebra.SpectralBooks.TrivialSlots
import OAI.LinearAlgebra.SpectralBooks.Spectrum
import OAI.LinearAlgebra.SpectralBooks.NatSpectralExponent

/-! # The value of a diagonal supported on a subset of sites

The site set is partitioned into occupied sites `S` and auxiliary sites `O`.
The spectral point and its normalizing diagonal live on the entire set.
Multiplicativity and local coordinate projections force the value on the
partial diagonal to be a fixed power of its dimension.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

open scoped NNReal

noncomputable section

variable (S O K : Type*) [Fintype S] [Fintype O] [Nonempty S] [CommSemiring K]

/-- A common label on `S`, with one-dimensional slots on `O`. -/
def Raw.supportDiagonal (α : Type) [Fintype α] : Raw.{0} (S ⊕ O) K :=
  Raw.withTrivial O (Raw.diagonal S K α)

/-- The partial diagonals form a multiplicative family of tensor classes. -/
def supportDiagonalHom : ℕ →* TensorClass.{0} (S ⊕ O) K where
  toFun n := ofRaw (Raw.supportDiagonal S O K (Fin n))
  map_one' := by
    have he := (Raw.diagonal_equiv S K (Equiv.ofUnique (Fin 1) PUnit))
    have hu := Raw.diagonal_unit_equivalent.{0} S K
    have h (X Y : Raw.{0} S K) (hXY : X.Equivalent Y) :
        ofRaw (Raw.withTrivial O X) = ofRaw (Raw.withTrivial O Y) :=
      ofRaw_eq_iff.mpr ⟨Raw.withTrivial_restricts O hXY.1, Raw.withTrivial_restricts O hXY.2⟩
    exact (h _ _ he).trans ((h _ _ hu).trans
      (ofRaw_eq_iff.mpr (Raw.withTrivial_one_equivalent O)))
  map_mul' n m := by
    have he := Raw.diagonal_equiv S K (finProdFinEquiv (m := n) (n := m)).symm
    have hm := (Raw.diagonal_product_equivalent (I := S) (K := K) (α := Fin n) (β := Fin m))
    have h (X Y : Raw.{0} S K) (hXY : X.Equivalent Y) :
        ofRaw (Raw.withTrivial O X) = ofRaw (Raw.withTrivial O Y) :=
      ofRaw_eq_iff.mpr ⟨Raw.withTrivial_restricts O hXY.1, Raw.withTrivial_restricts O hXY.2⟩
    exact (h _ _ he).trans ((h _ _ hm).symm.trans
      (ofRaw_eq_iff.mpr (Raw.withTrivial_mul_equivalent O _ _)))

/-- Increasing the number of labels can only increase a partial diagonal. -/
theorem supportDiagonalHom_mono : Monotone (supportDiagonalHom S O K) := by
  intro n m h
  exact Raw.withTrivial_restricts O (Raw.diagonal_restricts_of_embedding S K (Fin.castLEEmb h))

/-- For any normalized spectral point on all sites, the log value of the
`q`-diagonal on `S` equals the value of the binary diagonal times `log₂ q`.
This applies to arbitrary positive integers, including nonsquares and nonpowers of two. -/
theorem supportDiagonal_log_price
    (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (S ⊕ O) K → _ → Prop))
    {q : ℕ} (hq : 0 < q) :
    Real.logb 2 (f.val (ofRaw (Raw.supportDiagonal S O K (Fin q))) : ℝ) =
      Real.logb 2 (f.val (ofRaw (Raw.supportDiagonal S O K (Fin 2))) : ℝ) * Real.logb 2 q := by
  let v := (normalizedSpectrum.toRingHom f).toMonoidHom.comp (supportDiagonalHom S O K)
  apply spectral_natCast_logb (A := ℕ) (v := v) _ q hq
  intro a b _ hab
  exact f.property.2.2.2.2 _ _ (supportDiagonalHom_mono S O K hab)

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
