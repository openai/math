import OAI.Computability.VPVNP.HardnessCircuitRepresentation
import OAI.Computability.VPVNP.HardnessWitness
import OAI.Computability.VPVNP.VerifierFamily

/-!
# VNP-completeness of the integer family

A VNP summand has a polynomial-size ordered-parse CNF presentation. Copying each selected
production flag separates its scalar and variable labels. Witness variables become free Boolean
bits constrained by their selected occurrences. This leaves only variable and scalar projection
weights. The universal coefficient machine can check the resulting CNF by querying its payload.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Hardness

open MvPolynomial HardnessCNF

variable {F : Type*} [Field F] {V : ℕ → Type} [∀ n, Fintype (V n)]

/-- Every VNP family has a CNF presentation with polynomially many bits and literals.
Each selected bit contributes a single variable or a single scalar. -/
theorem exists_weightedCNF_of_isVNP (p : Family F V) (hp : IsVNP p) :
    ∃ (k : ℕ → ℕ) (φ : ∀ n, CNF (k n)) (weights : ∀ n, Projection F (Fin (k n)) (V n)),
      PolynomiallyBounded k ∧ PolynomiallyBounded (fun n => literalCount (φ n)) ∧
        ∀ n, weightedCNF (φ n) (fun i => (weights n i).elim X C) = p n := by
  obtain ⟨W, inst, g, hW, hg, he⟩ := hp.2
  let : ∀ n, Fintype (W n) := inst
  obtain ⟨m, hk, hlit, hm⟩ := exists_markedCNF_of_isVP g hg
  refine ⟨fun n => HardnessWitness.width (m n).width (W n),
    fun n => HardnessWitness.augment (m n).clauses (m n).label,
    fun n => HardnessWitness.augmentedWeight (m n).scalar (m n).label, ?_, ?_, ?_⟩
  · exact hk.add (hk.add hW)
  · exact (hlit.add ((PolynomiallyBounded.const 6).mul hk)).of_le
      fun n => HardnessWitness.literalCount_augment_le (m n).clauses (m n).label
  · intro n
    rw [he n, ← hm n]
    exact (HardnessWitness.sum_witnessValue_weightedCNF (m n).clauses (m n).scalar (m n).label).symm

/-- Each VNP family is a p-projection of the explicit universal integer family
after casting coefficients to the same field. -/
theorem pProjects_P_of_isVNP (p : Family F V) (hp : IsVNP p) :
    PProjects p (fun n => map (Int.castRingHom F) (P n)) := by
  obtain ⟨k, φ, weights, hk, hlit, he⟩ := exists_weightedCNF_of_isVNP p hp
  rw [← funext he]
  exact weightedCNF_PProjects φ weights hk hlit

end Hardness

section

/-- The VNP-completeness assertion of Theorem 1.1 for every field, with arbitrary field
constants and variable-or-constant projections of formal polynomials. -/
theorem P_vnpComplete (F : Type*) [Field F] :
    VNPComplete (σ := fun n => Fin n × Bool) (fun n => MvPolynomial.map (Int.castRingHom F) (P n)) :=
  ⟨P_isVNP F, fun _ _ p hp => Hardness.pProjects_P_of_isVNP p hp⟩

end

end VPVNP
end Computability
end OAI
