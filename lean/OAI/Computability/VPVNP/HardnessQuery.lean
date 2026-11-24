import OAI.Computability.VPVNP.QueryPrefix
import OAI.Computability.VPVNP.Pinning
import OAI.Computability.VPVNP.PolynomialBounds
import OAI.Computability.VPVNP.ProjectionComposition

/-!
# Weighted Boolean predicates as projections of the universal family

A finite query program reads the bits of a proposed assignment. Each selected
bit contributes its assigned weight, which may be a scalar or a formal variable.
Pinning the literal program prefix and projecting the payload gives the sum of
those products over the accepted assignments, in every characteristic.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {R τ : Type*} [CommRing R] {k : ℕ}

/-- The formal generating polynomial of a Boolean predicate with variable or scalar weights. -/
noncomputable def weightedPredicate (accept : (Fin k → Bool) → Bool)
    (weight : Projection R (Fin k) τ) : MvPolynomial τ R :=
  ∑ x, if accept x then ∏ i, if x i then (weight i).elim X C else 1 else 0

theorem weightedPredicate_eq_projection (accept : (Fin k → Bool) → Bool)
    (weight : Projection R (Fin k) τ) :
    weight.hom (booleanPolynomial fun x => ((accept x).toNat : R)) =
      weightedPredicate accept weight := by
  classical
  simp only [Projection.hom, booleanPolynomial, weightedPredicate, map_sum, map_mul,
    map_prod, eval₂Hom_C, apply_ite, eval₂Hom_X', map_one]
  apply Finset.sum_congr rfl
  intro x _
  cases h : accept x <;> simp

/-- For a single weighted query program the source length is bounded explicitly
in its state count, query budget, and payload length. -/
theorem weightedQuery_projection {Q : Type*} [Fintype Q] (q : QueryProgram k Q)
    (fuel : ℕ) (weight : Projection R (Fin k) τ) :
    ∃ n, n ≤ 1000 * ((fuel + 1) * Fintype.card Q * (k + 1) + 1) ^ 2 + k ∧
      ∃ φ : Projection R (Fin n × Bool) τ,
        φ.hom (MvPolynomial.map (Int.castRingHom R) (P n)) =
          weightedPredicate (fun x => q.eval x fuel q.start) weight := by
  obtain ⟨l, bits, hsize, hcount⟩ := QueryMachine.exists_prefix q fuel
  let pin := pinVariables (R := R) bits (Equiv.refl (Fin k))
  have hp : pin.hom (MvPolynomial.map (Int.castRingHom R) (P (l + k))) =
      booleanPolynomial (fun x => ((q.eval x fuel q.start).toNat : R)) := by
    rw [map_P]
    apply pairedPolynomial_pin
    intro x
    exact congrArg (fun b : ℕ => (b : R)) (hcount x)
  refine ⟨l + k, Nat.add_le_add_right hsize k, weight.comp pin, ?_⟩
  rw [Projection.hom_comp, RingHom.comp_apply, hp, weightedPredicate_eq_projection]

/-- A polynomial-size family of query predicates gives one p-projection, including
all the finite initial lengths. Weights may be chosen independently at each length. -/
theorem weightedQuery_PProjects {F : Type*} [Field F] {τ : ℕ → Type}
    {k fuel : ℕ → ℕ} {Q : ℕ → Type} [∀ n, Fintype (Q n)]
    (q : ∀ n, QueryProgram (k n) (Q n)) (weights : ∀ n, Projection F (Fin (k n)) (τ n))
    (hk : PolynomiallyBounded k) (hf : PolynomiallyBounded fuel)
    (hq : PolynomiallyBounded fun n => Fintype.card (Q n)) :
    PProjects (fun n => weightedPredicate (fun x => (q n).eval x (fuel n) (q n).start) (weights n))
      (fun n => MvPolynomial.map (Int.castRingHom F) (P n)) := by
  choose r hr φ hφ using fun n => weightedQuery_projection (q n) (fuel n) (weights n)
  refine ⟨r, ?_, fun n => ⟨φ n, hφ n⟩⟩
  have hcontrols := ((hf.add (.const 1)).mul hq).mul (hk.add (.const 1))
  exact (((PolynomiallyBounded.const 1000).mul ((hcontrols.add (.const 1)).pow 2)).add hk).of_le hr

end VPVNP
end Computability
end OAI
