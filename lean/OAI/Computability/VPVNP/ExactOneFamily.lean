import OAI.Computability.VPVNP.CNFNormalization
import OAI.Computability.VPVNP.ExactOnePadding
import OAI.Computability.VPVNP.Hardness

/-!
# Polynomial-size exact-one presentations of VNP families

The weighted CNF for a VNP summand can be replaced by exact-one clauses
without changing its generating polynomial. Clause normalization bounds the
number of clause vertices used by the graph reductions. A fixed false bit
gives every instance at least one variable.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF MvPolynomial

variable {F : Type*} [Field F] {V : ℕ → Type} [∀ n, Fintype (V n)]

/-- The Boolean variables carry only projection labels. Variable count,
clause count and literal-occurrence count are all polynomially bounded. -/
theorem exists_family_of_isVNP (p : Family F V) (hp : IsVNP p) :
    ∃ (k : ℕ → ℕ) (φ : ∀ n, CNF (k n)) (w : ∀ n, Projection F (Fin (k n)) (V n)),
      (∀ n, 0 < k n) ∧ PolynomiallyBounded k ∧
      PolynomiallyBounded (fun n => (φ n).length) ∧
      PolynomiallyBounded (fun n => literalCount (φ n)) ∧
      ∀ n, weightedExactOne (φ n) (fun i => (w n i).elim X C) = p n := by
  obtain ⟨k, φ, w, hk, hl, hφ⟩ := Hardness.exists_weightedCNF_of_isVNP p hp
  let ψ := fun n => normalizeClauses (φ n)
  obtain ⟨hL, hlen⟩ := normalizeClauses_polynomial_bounds φ hl
  obtain ⟨hwidth, hocc⟩ := polynomial_bounds ψ hk hL
  refine ⟨fun n => width (ψ n) + 1, fun n => pad (augment (ψ n)),
    fun n => padProjection (augmentProjection (ψ n) (w n)), fun _ => Nat.succ_pos _,
    hwidth.add (.const 1), ?_, ?_, ?_⟩
  · have hrows := (hlen.add (hL.pow 2)).of_le (fun n => length_augment_le (ψ n))
    simpa only [length_pad] using hrows.add (.const 1)
  · simpa only [literalCount_pad] using hocc.add (.const 1)
  · intro n
    rw [weightedExactOne_padProjection]
    simp_rw [augmentProjection_eval, weightedExactOne_augment, ψ, weightedCNF_normalizeClauses]
    exact hφ n

end ExactOne

end VPVNP
end Computability
end OAI
