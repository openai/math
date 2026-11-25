import OAI.Computability.BorderVNP.TransferIntegerUniform
import OAI.Computability.BorderVNP.TransferIntegerCNF

/-!
# Characteristic-independent projection orders for the signed witness

The same integer Boolean formula supplies the graph instances over every field.
For directed Hamiltonian cycles all coefficients are integral. For permanent
the equality gadget uses the inverse of two.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open VPVNP MvPolynomial

universe u

/-- The §12 projections use common source orders, each at least two so that
the one-vertex padding projections apply at every source index. -/
theorem uniform_matrix_projections_with_order :
    ∃ jHC jPer : ℕ → ℕ, PolynomiallyBounded jHC ∧ PolynomiallyBounded jPer ∧
      (∀ n, 2 ≤ jHC n ∧ 2 ≤ jPer n) ∧
      (∀ n (F : Type u) [Field F],
        ∃ ρ : Projection F (Fin (jHC n) × Fin (jHC n)) (Fin n × Bool),
          ρ.hom (hamiltonianCyclePolynomial F (jHC n)) = map (Int.castRingHom F) (Pstar n)) ∧
      (∀ n (F : Type u) [Field F] (q : ℕ) [CharP F q], q ≠ 2 →
        ∃ ρ : Projection F (Fin (jPer n) × Fin (jPer n)) (Fin n × Bool),
          ρ.hom (permanentPolynomial F (jPer n)) = map (Int.castRingHom F) (Pstar n)) := by
  obtain ⟨_, φ, w, hk, hl, he⟩ := signed_weightedCNF
  exact uniform_matrix_projections_of_weightedCNF Pstar φ w hk hl he

/-- Before fixing the field, one can fix a polynomially bounded source-order
function for each graph family. -/
theorem uniform_matrix_projections :
    ∃ jHC jPer : ℕ → ℕ, PolynomiallyBounded jHC ∧ PolynomiallyBounded jPer ∧
      (∀ n (F : Type u) [Field F],
        ∃ ρ : Projection F (Fin (jHC n) × Fin (jHC n)) (Fin n × Bool),
          ρ.hom (hamiltonianCyclePolynomial F (jHC n)) = map (Int.castRingHom F) (Pstar n)) ∧
      (∀ n (F : Type u) [Field F] (q : ℕ) [CharP F q], q ≠ 2 →
        ∃ ρ : Projection F (Fin (jPer n) × Fin (jPer n)) (Fin n × Bool),
          ρ.hom (permanentPolynomial F (jPer n)) = map (Int.castRingHom F) (Pstar n)) := by
  obtain ⟨j, t, hj, ht, _, h, p⟩ := uniform_matrix_projections_with_order.{u}
  exact ⟨j, t, hj, ht, h, p⟩

end BorderVNP
end Computability
end OAI
