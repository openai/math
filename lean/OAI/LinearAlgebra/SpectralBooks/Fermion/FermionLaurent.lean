import OAI.LinearAlgebra.SpectralBooks.Fermion.WickNormalMatrix
import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionCutoff

/-! # The equal-energy Laurent coefficient of the finite fermionic supercommutator -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Filter LaurentPolynomial

/-- The two truncated product expansions at a fixed equal-energy pair of
states. The states are held fixed while the occupied-mode cutoff goes to infinity. -/
def LaurentCrossingIdentity : Prop :=
  ∀ (i j a b : State), i.Nonempty → i.card = j.card → weight a = weight b → ∀ s : ℤ,
    ∀ᶠ N : ℕ in atTop, ∀ (α β : FockState N), α.val = a → β.val = b →
      (((1 - T 1) ^ order (weight i) (weight j)) *
        ((fieldMatrix N false i * fieldMatrix N true j) α β -
          (-1 : LaurentPolynomial ℤ)^(i.card*j.card) *
            ((fieldMatrix N true j * fieldMatrix N false i) α β))).coeff s =
        pairing i j * (if a = b then 1 else 0)

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
