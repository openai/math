import OAI.Computability.VPVNP.CircuitGrammar
import OAI.Computability.VPVNP.GrammarLabels

/-!
# The coefficient equations at a small-circuit length

At a length where the universal polynomial has a circuit of the stipulated size, the
positive-degree grammar of Section 8.1 admits one assignment of all labels satisfying
every paired coefficient equation simultaneously. The width and start slot below are
those of the paper. The start slot numbered one there is zero in Lean.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

/-- The width from Section 8.1 accommodates all variables, gates and the designated output. -/
theorem parseSlots_le (n C s : ℕ) (hn : 2 ≤ n) (hC : 1 ≤ C) (hs : s ≤ n ^ C) :
    Fintype.card (Fin n × Bool) + s + 1 ≤ n ^ (C + 5) := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, pow_add]
  have hnC : n ≤ n ^ C := Nat.le_self_pow (by omega) n
  have h5 : 4 ≤ n ^ 5 := le_trans (by decide : 4 ≤ 2 ^ 5) (Nat.pow_le_pow_left hn 5)
  have := Nat.mul_le_mul_left (n ^ C) h5
  omega

/-- A small circuit for the universal polynomial gives an assignment in its own
coefficient ring whose output entries are exactly the machine path counts. -/
theorem exists_pathCount_parseGrammar {R : Type*} [CommRing R] {n C s : ℕ}
    (hn : 2 ≤ n) (hC : 1 ≤ C) (hs : s ≤ n ^ C)
    (c : Circuit R (Fin n × Bool) s)
    (hc : c.polynomial = map (Int.castRingHom R) (P n)) :
    ∃ G : ParseGrammar R (Fin n × Bool) (Fin (n ^ (C + 5))) n,
      ∀ x : Fin n → Bool,
        (G.eval ⟨n - 1, by omega⟩ ⟨0, pow_pos (by omega) _⟩).coeff (pairedExponent x) =
          (acceptingCount x : R) := by
  obtain ⟨G, hG⟩ := c.exists_parseGrammar_fin n (n ^ (C + 5)) (parseSlots_le n C s hn hC hs)
  refine ⟨G, fun x ↦ ?_⟩
  have hout := hG ⟨n - 1, by omega⟩
  have hdeg : n - 1 + 1 = n := by omega
  rw [hout, hdeg, hc, map_P, homogeneousComponent_eq_self (pairedPolynomial_isHomogeneous _),
    coeff_pairedPolynomial]

/-- Equation (8.1): one assignment to the universal integer parameter polynomials
works for all queried words. The assignment is obtained from the actual circuit. -/
theorem pathCount_labelEquations {R : Type*} [CommRing R] {n C s : ℕ}
    (hn : 2 ≤ n) (hC : 1 ≤ C) (hs : s ≤ n ^ C)
    (c : Circuit R (Fin n × Bool) s)
    (hc : c.polynomial = map (Int.castRingHom R) (P n)) :
    ∃ labels : GrammarLabel (Fin n × Bool) (Fin (n ^ (C + 5))) n → R,
      ∀ x : Fin n → Bool,
        eval₂Hom (Int.castRingHom R) labels
          (labelQuery ⟨n - 1, by omega⟩ ⟨0, pow_pos (by omega) _⟩ x) = (acceptingCount x : R) := by
  obtain ⟨G, hG⟩ := exists_pathCount_parseGrammar hn hC hs c hc
  exact ⟨G.labelValue, fun x ↦ (G.specialize_labelQuery _ _ x).trans (hG x)⟩

end VPVNP
end Computability
end OAI
