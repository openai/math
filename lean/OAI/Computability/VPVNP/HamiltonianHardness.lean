import OAI.Computability.VPVNP.HCWeighted
import OAI.Computability.VPVNP.ExactOneFamily
import OAI.Computability.VPVNP.HamiltonianMembership
import OAI.Computability.VPVNP.CompletePolynomials
import OAI.Computability.VPVNP.CompleteFieldDescent

/-!
# Hamiltonian-cycle completeness and the transfer in Corollary 1.2

The exact-one presentation of an arbitrary VNP family projects from a directed
Hamiltonian-cycle polynomial of polynomially bounded order. For the paper's
integer family this is the projection in the direction used in §15.1.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {F : Type*} [Field F] {V : ℕ → Type} [∀ n, Fintype (V n)]

/-- The directed Hamiltonian-cycle polynomial is hard under literal p-projections in all
characteristics. The graph construction uses the Boolean variables, clauses and occurrences
of the weighted exact-one presentation. -/
theorem pProjects_hamiltonian_of_isVNP (p : Family F V) (hp : IsVNP p) :
    PProjects p (hamiltonianCyclePolynomial F) := by
  obtain ⟨k, φ, w, hk, hwidth, hclauses, hlits, he⟩ := ExactOne.exists_family_of_isVNP p hp
  refine ⟨fun n => k n * (3 * HardnessCNF.literalCount (φ n) + 4) + (φ n).length,
    (hwidth.mul (((PolynomiallyBounded.const 3).mul hlits).add (.const 4))).add hclauses, ?_⟩
  intro n
  obtain ⟨ψ, hψ⟩ := HCGadget.weighted_projection (φ n) (hk n) (w n)
  exact ⟨ψ, hψ.trans (he n)⟩

theorem hamiltonian_vnpComplete (F : Type*) [Field F] : VNPComplete (hamiltonianCyclePolynomial F) :=
  ⟨hamiltonian_isVNP F, fun _ _ p hp => pProjects_hamiltonian_of_isVNP p hp⟩

/-- The explicit integer family projects from directed Hamiltonian cycles, over every field. -/
theorem P_pProjects_hamiltonian (F : Type*) [Field F] :
    PProjects (fun n => map (Int.castRingHom F) (P n)) (hamiltonianCyclePolynomial F) :=
  pProjects_hamiltonian_of_isVNP _ (P_isVNP F)

/-- The directed Hamiltonian-cycle assertion of Corollary 1.2 follows from the eventual
lower bound for `P` over one algebraically closed field of the specified characteristic. -/
theorem hamiltonian_uniform_of_P {K : Type*} [Field K] [IsAlgClosed K]
    (q : ℕ) [CharP K q]
    (h : EventuallySuperpolynomial fun n => circuitSize (map (Int.castRingHom K) (P n)))
    (C : ℕ) :
    ∃ N, ∀ m ≥ N, ∀ (F : Type*) [Field F] [CharP F q],
      m ^ C < circuitSize (hamiltonianCyclePolynomial F m) := by
  obtain ⟨N, hN⟩ := hamiltonian_bound_of_pProjects (P_pProjects_hamiltonian K) h C
  exact ⟨N, hamiltonianCyclePolynomial_uniform_bound (K := K) q C N hN⟩

end VPVNP
end Computability
end OAI
