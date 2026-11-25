import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping

/-! # Powers of placed diagonals

A diagonal whose common label consists of an `n`-tuple of symbols is a
product of `n` single-symbol diagonals, at every placement of its slots.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

variable {A I : Type} [Fintype A] [Nonempty A] [Fintype I] [Nonempty I]
variable (K : Type*) [CommSemiring K] (σ : A → I)

/-- A common label with `b ^ n` possible values yields the `n`th power of the
placed `b`-symbol diagonal. -/
theorem ofRaw_group_diagonal_fin_pow (b n : ℕ) :
    ofRaw ((Raw.diagonal A K (Fin (b ^ n))).group σ) =
      ofRaw ((Raw.diagonal A K (Fin b)).group σ) ^ n := by
  change groupMulHom σ (ofRaw (Raw.diagonal A K (Fin (b ^ n)))) =
    groupMulHom σ (ofRaw (Raw.diagonal A K (Fin b))) ^ n
  rw [ofRaw_diagonal_fin_eq_natCast, ofRaw_diagonal_fin_eq_natCast, Nat.cast_pow, map_pow]

/-- The same power identity with the symbols presented as a word of length `n`. -/
theorem ofRaw_group_diagonal_fun_fin (D : Type) [Fintype D] (n : ℕ) :
    ofRaw ((Raw.diagonal A K (Fin n → D)).group σ) =
      ofRaw ((Raw.diagonal A K D).group σ) ^ n := by
  change groupMulHom σ (ofRaw (Raw.diagonal A K (Fin n → D))) =
    groupMulHom σ (ofRaw (Raw.diagonal A K D)) ^ n
  rw [ofRaw_diagonal_eq_natCast, ofRaw_diagonal_eq_natCast, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, map_pow]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
