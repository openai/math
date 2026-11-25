import OAI.Computability.NearSquareRoot.SynchronizedControlledWalsh
import OAI.Computability.NearSquareRoot.SynchronizedHalfTables

/-! # Routing a radix stage to the fixed physical half-selector bit -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open IntegerMultiplication Net.Walsh Matrix SynchronizedPair

variable {k : ℕ}

/-- Route the radix bit to the outer half selector in the doubled address layout. -/
def internalRoute (i : Fin k) : Equiv.Perm (Fin (2 ^ k) ⊕ Fin (2 ^ k)) :=
  dilationAddress.trans ((swapHalf i).trans dilationAddress.symm)

theorem internalRoute_address (i : Fin k) (x : Fin (2 ^ k) ⊕ Fin (2 ^ k)) :
    dilationAddress (internalRoute i x) =
      (rankBits (dilationAddress x).2 i, withBit i (dilationAddress x).2 (dilationAddress x).1) := by
  change dilationAddress (dilationAddress.symm ((swapHalf i) (dilationAddress x))) = _
  exact dilationAddress.apply_symm_apply _

/-- Both directions of the conjugating permutation use exactly the same query. -/
@[simp] theorem internalRoute_symm (i : Fin k) : (internalRoute i).symm = internalRoute i := by
  ext x
  rfl

private theorem withBit_eq_iff (i : Fin k) (r t : Fin (2 ^ k)) (b c : B) :
    withBit i r b = withBit i t c ↔ b = c ∧ (r = t ∨ partnerRank i r = t) := by
  rw [← sameSpectators_iff]
  constructor
  · intro h
    have dig (j : Fin k) := congrArg (fun x ↦ rankBits x j) h
    simp only [rankBits_withBit] at dig
    exact ⟨by simpa using dig i, fun j hj ↦ by simpa [hj] using dig j⟩
  · rintro ⟨rfl, h⟩
    apply ((Function.LeftInverse.injective (fun u ↦ localV_rankBits (k := k) u)) :
      Function.Injective (rankBits (k := k)))
    funext j
    by_cases hj : j = i
    · simp [rankBits_withBit, hj]
    · simp [rankBits_withBit, hj, h j hj]

private theorem bothHalves_entry (i : Fin k) (x y : Fin (2 ^ k) ⊕ Fin (2 ^ k)) :
    bothHalvesWalsh i x y =
      (if (dilationAddress x).1 = (dilationAddress y).1 then
        radixGateMatrix k (.butterfly i) (dilationAddress x).2 (dilationAddress y).2 else 0) := by
  cases x <;> cases y <;> simp [bothHalvesWalsh, dilationAddress]

/-- Conjugation by the actual address permutation implements the internal
Walsh slot on both halves, with the physical transform always on the same bit. -/
theorem bothHalvesWalsh_route (i : Fin k) :
    bothHalvesWalsh i = (internalRoute i).toPEquiv.toMatrix * physicalHalfWalsh *
      (internalRoute i).symm.toPEquiv.toMatrix := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext x y
  simp only [Matrix.submatrix_apply, id_eq, Equiv.symm_symm, physicalHalfWalsh,
    internalRoute_address, halfWalsh, bothHalves_entry,
    radixGateMatrix_butterfly_apply]
  change _ = if withBit i (dilationAddress x).2 (dilationAddress x).1 =
      withBit i (dilationAddress y).2 (dilationAddress y).1 then
    walsh (rankBits (dilationAddress x).2 i) (rankBits (dilationAddress y).2 i) else 0
  have he := withBit_eq_iff i (dilationAddress x).2 (dilationAddress y).2
    (dilationAddress x).1 (dilationAddress y).1
  split_ifs <;> tauto

end ShortFourier

end NearSquareRoot
end Computability
end OAI
