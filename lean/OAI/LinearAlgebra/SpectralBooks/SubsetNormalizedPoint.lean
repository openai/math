import OAI.LinearAlgebra.SpectralBooks.SubsetPriceOrdinary
import OAI.LinearAlgebra.SpectralBooks.SpectralNormalization

/-!
# The spectral point on a noncollapsed subset of sites

For an ambient spectral point, extending tensors on the occupied sites by
scalar slots gives a multiplicative evaluation. The reciprocal power of its
binary diagonal exponent is a normalized spectral point on the occupied sites.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

open Real
open scoped NNReal
noncomputable section

variable {S O K : Type*} [Fintype S] [Fintype O] [Nonempty S] [CommSemiring K]
  (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (S ⊕ O) K → _ → Prop))

/-- The binary diagonal price on the occupied sites in units of the ambient price. -/
def subsetDiagonalExponent : ℝ := logb 2 (φ.val (ofRaw (Raw.supportDiagonal S O K (Fin 2))))

/-- Normalizing an ambient point on the sites `S` gives a spectral point
on the tensor semiring of `S`. -/
def normalizedSubsetPoint (hp : 0 < subsetDiagonalExponent φ) :
    normalizedSpectrum ((· ≤ ·) : TensorClass.{0} S K → _ → Prop) := by
  let v := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (withTrivialHom (S := S) O)
  have hm : Monotone v := fun _ _ h => φ.2.2.2.2.2 _ _ (withTrivialHom_mono h)
  have hn {a b : ℕ} (_ : 0 < a) (h : a ≤ b) : v (a : TensorClass.{0} S K) ≤ v b := by
    apply hm
    rw [← ofRaw_diagonal_fin_eq_natCast S K a, ← ofRaw_diagonal_fin_eq_natCast S K b]
    exact Raw.diagonal_restricts_of_embedding S K (Fin.castLEEmb h)
  have hdiag : logb 2 (v 2) = subsetDiagonalExponent φ := congrArg (fun z => logb 2 (φ.val z))
    (withTrivialHom_natCast (S := S) (O := O) (K := K) 2)
  let F : TensorClass.{0} S K →+* ℝ≥0 := normalizeSpectralHom v hp (fun n hn' => by
    rw [← hdiag]; exact spectral_natCast_eq_rpow v hn n hn')
    ((congrArg φ.val withTrivialHom_zero).trans φ.2.1)
    (fun x y => (φ.2.2.2.2.2 _ _ (withTrivialHom_add_le x y)).trans_eq (φ.2.2.2.1 _ _))
    (fun x y => hm (by simpa only [add_zero] using add_mono (le_refl x) (zero_le_tensor y)))
  exact ⟨F, map_zero F, map_one F, map_add F, map_mul F, fun _ _ h =>
    NNReal.rpow_le_rpow (hm h) (inv_nonneg.mpr hp.le)⟩

theorem normalizedSubsetPoint_apply (hp : 0 < subsetDiagonalExponent φ) (X : TensorClass.{0} S K) :
    (normalizedSubsetPoint φ hp).val X =
      φ.val (withTrivialHom O X) ^ (subsetDiagonalExponent φ)⁻¹ := rfl

/-- The ambient price pulled back to `S` is the price of the binary diagonal
on `S` times the logarithm of the normalized subset point. -/
theorem normalizedSubsetPoint_price (hp : 0 < subsetDiagonalExponent φ)
    (X : TensorClass.{0} S K) (c : ℝ) :
    c * logb 2 (φ.val (withTrivialHom O X)) =
      (c * subsetDiagonalExponent φ) * logb 2 ((normalizedSubsetPoint φ hp).val X) := by
  rw [normalizedSubsetPoint_apply, NNReal.coe_rpow]
  by_cases hz : φ.val (withTrivialHom O X) = 0
  · simp [hz, Real.zero_rpow (inv_ne_zero hp.ne')]
  have hpos : 0 < (φ.val (withTrivialHom O X) : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hz)
  rw [Real.logb_rpow_eq_mul_logb_of_pos hpos]
  field_simp

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
