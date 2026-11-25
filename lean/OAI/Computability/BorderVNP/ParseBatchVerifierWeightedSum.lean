import OAI.Computability.BorderVNP.ParseBatchVerifierKeys

/-!
# Contraction of the physical parse and histogram guesses

Sum over every bit of the flat witness input. For a valid tuple of parses exactly one
rank-and-count assignment passes the checks. Its count wires determine the unary powers
in the product, so no auxiliary multiplicity is introduced into the integer coefficients.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchVerifier

open MvPolynomial VPVNP VPVNP.ParseGrammar ParseRecords ParseBatch ParseBatchCounts
open scoped Classical

variable {m g n r : ℕ}

/-- A flat physical parse-guess bit indexed by query, preorder row, and field position. -/
abbrev RawPin {n : ℕ} (m g r : ℕ) (d : Fin n) :=
  Fin r × Fin (2 * d.val + 1) × BitSlot (recordWidth m g n)

/-- The complete auxiliary input with a rank word and a count word for each potential key. -/
abbrev AuxPin {n : ℕ} (m g r : ℕ) (d : Fin n) :=
  ArithmeticPin (2 ^ labelWidth m g n) (histogramWidth m g r d)

/-- Regard a flat raw-bit array as a tuple of query blocks. -/
def decodeRaw (d : Fin n) (raw : RawPin m g r d → Bool) : Guess m g n r d :=
  fun i j s => raw (i, j, s)

private def rawEquiv (d : Fin n) : (RawPin m g r d → Bool) ≃ Guess m g n r d where
  toFun := decodeRaw d
  invFun := fun bs ij => bs ij.1 ij.2.1 ij.2.2
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Unary parameter factors selected by the actual guessed count wires. -/
noncomputable def guessedWeight (d : Fin n) (aux : AuxPin m g r d → Bool) :
    MvPolynomial (GrammarLabel (Fin m × Bool) (Fin g) n) ℤ :=
  ∏ t, ∏ j : Fin (Nat.clog 2 (r * (2 * d.val + 1) + 1)),
    if aux (weightPin d t j) then X t ^ (2 ^ j.val) else 1

/-- The unique accepted auxiliary words apply the factors for the actual multiplicities. -/
theorem guessedWeight_canonical (d : Fin n) (bs : Guess m g n r d) :
    guessedWeight d (canonicalGuess (histogramLayout m g r d) (occurrenceBits bs)) = bitWeight d bs := by
  simp only [guessedWeight, bitWeight, canonical_weightPin]

/-- Splitting a physical witness on disjoint pin types into independent Boolean guesses
introduces no change to the sum. -/
private theorem sum_split_pins {A B M : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] [DecidableEq (A ⊕ B)] [AddCommMonoid M]
    (f : (A ⊕ B → Bool) → M) :
    ∑ z, f z = ∑ x : A → Bool, ∑ y : B → Bool, f (Sum.elim x y) := by
  calc
    _ = ∑ p : (A → Bool) × (B → Bool), f (Sum.elim p.1 p.2) :=
      ((Equiv.sumArrowEquivProdArrow A B Bool).symm.sum_comp f).symm
    _ = _ := Fintype.sum_prod_type _

/-- The checked Boolean acceptance condition and the prescribed unary factors contract to
the product of the original coefficient queries, with every physical guessed bit summed. -/
theorem weighted_sum_of_accept (d : Fin n) (h : Fin g) (x : Fin r → Fin m → Bool)
    (test : ((Fin r × Fin m) ⊕ (RawPin m g r d ⊕ AuxPin m g r d) → Bool) → Bool)
    (ht : ∀ (raw : RawPin m g r d → Bool) (aux : AuxPin m g r d → Bool),
      test (Sum.elim (fun ij => x ij.1 ij.2) (Sum.elim raw aux)) = true ↔
        Accepted d h x (decodeRaw d raw) ∧
          aux = canonicalGuess (histogramLayout m g r d) (occurrenceBits (decodeRaw d raw))) :
    (∑ z : RawPin m g r d ⊕ AuxPin m g r d → Bool,
      if test (Sum.elim (fun ij => x ij.1 ij.2) z) then guessedWeight d (z ∘ Sum.inr) else 0) =
      ∏ i, labelQuery d h (x i) := by
  rw [product_eq_bit_sum]
  refine (sum_split_pins (A := RawPin m g r d) (B := AuxPin m g r d) (fun z =>
    if test (Sum.elim (fun ij => x ij.1 ij.2) z) then guessedWeight d (z ∘ Sum.inr) else 0)).trans ?_
  calc
    _ = ∑ raw : RawPin m g r d → Bool,
        if Accepted d h x (decodeRaw d raw) then bitWeight d (decodeRaw d raw) else 0 := by
      apply Finset.sum_congr rfl
      intro raw _
      simp only [ht, Sum.elim_comp_inr]
      by_cases accepted : Accepted d h x (decodeRaw d raw)
      · simp [accepted, guessedWeight_canonical]
      · simp [accepted]
    _ = _ := (rawEquiv d).sum_comp fun bs =>
      if Accepted d h x bs then bitWeight d bs else 0

end ParseBatchVerifier

end BorderVNP
end Computability
end OAI
