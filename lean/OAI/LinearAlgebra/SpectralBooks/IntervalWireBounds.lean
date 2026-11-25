import OAI.LinearAlgebra.SpectralBooks.SiteTensor.IntervalGenerators
import OAI.LinearAlgebra.SpectralBooks.OldSiteContraction
import OAI.LinearAlgebra.SpectralBooks.DiagonalContraction

/-! # Removing old factors and full diagonals from the interpolation bound

An embedded old tensor adds its old price exactly. Each full binary diagonal
adds one to the contraction price. Thus the upper bound and sharpness need
only be proved on the two wire factors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]

private theorem fullBinary_nonzero : (2 : TensorClass.{v} (Option I) K) ≠ 0 := by
  obtain ⟨v, hv⟩ := spectrum_nonempty.{v} (Option I) K
  let f := normalizedSpectrum.toRingHom ⟨v, hv⟩
  intro h
  have hf := congrArg f h
  rw [map_ofNat, map_zero] at hf
  norm_num at hf

/-- In logarithmic product notation, the full binary diagonal has one unit of
price for every normalized spectral point on the enlarged site set. -/
def intervalFullBinary : NonzeroProduct.{v} (Option I) K :=
  Additive.ofMul ⟨2, fullBinary_nonzero⟩

private theorem interval_contraction_split
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
    (A B : NonzeroProduct.{v} (Option I) K) (X : NonzeroProduct.{v} I K) (m n k : ℕ) :
    classContractionPrice φ (classOfProduct
      (intervalEval embedOldProduct A B intervalFullBinary (X, m, n, k))) =
      logPoint φ X + classContractionPrice φ (classOfProduct (m • A + n • B)) + (k : ℝ) := by
  let P := embedOldProduct X + (m • A + n • B)
  have he : intervalEval embedOldProduct A B intervalFullBinary (X, m, n, k) =
      k • intervalFullBinary + P := by
    change (embedOldProduct X + m • A + n • B) + k • intervalFullBinary = _
    rw [add_comm _ (k • intervalFullBinary), add_assoc (embedOldProduct X)]
  have hd : classOfProduct (k • intervalFullBinary + P) =
      (((2 ^ k : ℕ) : TensorClass.{v} (Option I) K)) * classOfProduct P := by
    change (2 : TensorClass.{v} (Option I) K)^k * _ = _
    rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [he, hd, classContractionPrice_natCast_mul φ (pow_pos (by decide : 0 < 2) _) P.toMul.property]
  rw [show classContractionPrice φ (classOfProduct P) = _ from
    classContractionPrice_embedOldProduct_add φ X (m • A + n • B)]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  exact add_comm _ _

/-- The costs of the two new wires suffice to prescribe their prices while
retaining all old log prices at the same spectral point. -/
theorem spectral_interval_of_wire_bounds
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
    (A B : NonzeroProduct.{v} (Option I) K) (la lb : ℝ) (ha : 0 ≤ la) (hb : 0 ≤ lb)
    (upper : ∀ m n : ℕ, classContractionPrice φ (classOfProduct (m • A + n • B)) ≤
      min (m : ℝ) n * (la + lb))
    (sharp : ∀ m : ℕ, (m : ℝ) * (la + lb) ≤
      classContractionPrice φ (classOfProduct (m • A + m • B))) :
    ∃ f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} (Option I) K → _ → Prop),
      (∀ X, logPoint f (embedOldProduct X) = logPoint φ X) ∧ logPoint f A = la ∧ logPoint f B = lb := by
  apply spectral_interval_of_contraction_formula φ embedOldProduct A B intervalFullBinary rfl la lb ha hb
  · intro X m n k
    rw [interval_contraction_split, Nat.cast_min]
    linarith [upper m n]
  · intro X m k
    rw [interval_contraction_split]
    linarith [sharp m]

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
