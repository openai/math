import OAI.Computability.BorderVNP.TransferIntegerCNF
import OAI.Computability.VPVNP.CNFNormalization

/-!
# Bounded signed clauses for the ordered two-pass verifier

Each true assignment bit contributes one, minus one, or one paired input variable.
There is one Boolean assignment per nonzero signed path. The number of bits, clauses
and literal occurrences are all bounded by fixed polynomials in the input length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace SignedCNF

open VPVNP VPVNP.HardnessCNF MvPolynomial

/-- The weighted CNF needed for the integer matrix substitution of Lemma 13.2. -/
theorem exists_Pstar_encoding :
    ∃ (k : ℕ → ℕ) (φ : ∀ n, CNF (k n)) (w : ∀ n, Fin (k n) → MvPolynomial (Fin n × Bool) ℤ),
      PolynomiallyBounded k ∧ PolynomiallyBounded (fun n => literalCount (φ n)) ∧
      PolynomiallyBounded (fun n => (φ n).length) ∧
      (∀ n i, w n i = 1 ∨ w n i = -1 ∨ ∃ z, w n i = X z) ∧
      ∀ n, weightedCNF (φ n) (w n) = Pstar n := by
  obtain ⟨k, φ, w, hk, hl, hw, he⟩ := signed_weightedCNF_units
  obtain ⟨hl', hc⟩ := normalizeClauses_polynomial_bounds φ hl
  refine ⟨k, fun n => normalizeClauses (φ n), fun n i => (w n i).elim X C, hk, hl', hc, ?_, ?_⟩
  · intro n i
    rcases hw n i with h | h | ⟨z, h⟩ <;> simp [h]
  · intro n
    rw [weightedCNF_normalizeClauses, he]

end SignedCNF

end BorderVNP
end Computability
end OAI
