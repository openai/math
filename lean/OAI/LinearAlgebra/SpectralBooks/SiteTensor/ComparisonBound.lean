import OAI.LinearAlgebra.SpectralBooks.ConcreteSpectrum

/-! # Bounding one tensor by copies of a nonzero tensor

A finite upper bound for tensor rank and a restriction to the unit from any
nonzero tensor give Strassen's boundedness condition for the restriction order.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v

variable {I K : Type*} [Fintype I] [Nonempty I]

instance [CommSemiring K] : IsOrderedAddMonoid (TensorClass.{v} I K) where
  add_le_add_left _ _ h _ := add_mono h le_rfl

instance [CommSemiring K] : IsOrderedMonoid (TensorClass.{v} I K) where
  mul_le_mul_left _ _ h _ := mul_mono h le_rfl

variable [Field K]

/-- Every tensor is a restriction of finitely many copies of any nonzero tensor. -/
theorem exists_le_nsmul_of_ne_zero (X Y : TensorClass.{v} I K) (hY : Y ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ X ≤ n • Y := by
  obtain ⟨r, hr⟩ := exists_le_natCast X
  have h : (r : TensorClass.{v} I K) ≤ r • Y := by
    simpa only [nsmul_one] using nsmul_le_nsmul_right (one_le_of_ne_zero hY) r
  refine ⟨r + 1, Nat.succ_pos _, (hr.trans h).trans ?_⟩
  simpa only [succ_nsmul, add_zero] using add_mono (le_refl (r • Y)) (zero_le_tensor Y)

/-- In multiplicative notation, the upper bound is a natural diagonal times the source. -/
theorem exists_le_natCast_mul_of_ne_zero (X Y : TensorClass.{v} I K) (hY : Y ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ X ≤ (n : TensorClass.{v} I K) * Y := by
  simpa only [nsmul_eq_mul] using exists_le_nsmul_of_ne_zero X Y hY

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
