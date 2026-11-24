import OAI.Computability.VPVNP.VerifierFamily
import OAI.Computability.VPVNP.HamiltonianProjection
import OAI.Computability.VPVNP.ProjectionClosure

/-! # VNP membership of the directed Hamiltonian cycle family -/

namespace OAI
namespace Computability
namespace VPVNP

theorem hamiltonian_isVNP (F : Type*) [Field F] :
    IsVNP (σ := fun n => Fin n × Fin n) (hamiltonianCyclePolynomial F) := by
  apply (P_isVNP F).of_pProjects (hamiltonian_PProjects F)
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    PolynomiallyBounded.id.mul PolynomiallyBounded.id

end VPVNP
end Computability
end OAI
