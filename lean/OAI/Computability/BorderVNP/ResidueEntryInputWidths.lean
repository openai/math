import OAI.Computability.BorderVNP.ResidueEntryInput

/-! # Widths and multiplicity of the residue query and guess tapes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryInput

open ResidueFourier ResidueEntryField ExactQuantumFactoring

variable {σ J : Type*} {idx D m d w b : ℕ}

/-- The fixed input consists of three offset exponent vectors, two addresses and the
gadget multiplicity words. -/
theorem query_card [Fintype σ] [Fintype J] :
    Fintype.card (Query σ idx D J m) =
      3*(Fintype.card (Option σ)*idx) + 2*Nat.clog 2 D + Fintype.card J*m := by
  simp [Query,ResidueIndex.Raw,Nat.add_assoc]

/-- The guess uses exactly one binary field register per coordinate and one threshold. -/
theorem guess_card [Fintype σ] :
    Fintype.card (Guess σ d w b) = Fintype.card (Option σ)*(d*w)+b := by
  simp [Guess]

/-- Exact arity of the shared entry verifier. -/
theorem input_card [Fintype σ] [Fintype J] :
    Fintype.card (Input σ idx D J m d w b) =
      (3*(Fintype.card (Option σ)*idx) + 2*Nat.clog 2 D + Fintype.card J*m) +
      (Fintype.card (Option σ)*(d*w)+b) := by
  unfold Input
  rw [Fintype.card_sum, query_card, guess_card]

/-- The private named tape enumerates every tuple of candidate limb words and every
threshold word exactly once, including invalid candidates rejected by the grid guard. -/
def guessEquiv (σ : Type*) (d w b : ℕ) :
    (Guess σ d w b → Bool) ≃ ((Option σ → LimbWords d w) × Fin (2^b)) :=
  let grid := (Equiv.curry _ _ _).trans ((Equiv.refl _).arrowCongr (limbWords d w))
  (Equiv.sumArrowEquivProdArrow _ _ _).trans
    (grid.prodCongr ((bitsEquiv b).trans BitVec.equivFin.toEquiv))

/-- The guess equivalence on an encoded tuple performs ordinary little-endian decoding. -/
theorem guessEquiv_encodeGuess (grid : Option σ → Fin (d*w) → Bool) (y : Fin b → Bool) :
    guessEquiv σ d w b (encodeGuess grid y) =
      (fun i => limbWords d w (grid i), ⟨value y,(bitsValue y).isLt⟩) := rfl

/-- The inverse of the guess equivalence selects the binary representation of each limb
word and of the threshold. -/
theorem guessEquiv_symm (z : Option σ → LimbWords d w) (y : Fin (2^b)) :
    (guessEquiv σ d w b).symm (z,y) =
      encodeGuess (fun i => (limbWords d w).symm (z i))
        (((bitsEquiv b).trans BitVec.equivFin.toEquiv).symm y) := rfl

end ResidueEntryInput

end BorderVNP
end Computability
end OAI
