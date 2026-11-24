import OAI.Computability.VPVNP.RefreshMonomialWitness
import OAI.Computability.VPVNP.RefreshProcedure
import OAI.Computability.VPVNP.CompressionMonomialHistory

/-!
# Refresh witnesses in the common template alphabet

Every scheduled refresh uses the second group of parameters in the fixed
equations. Its kernel witnesses record the label multiplicities at each port
for every choice of branch and half-wire arguments.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open NetworkKernel Refresh

variable {k : Type*} [Field k] {S : BlockSchedule k}
variable (B : S.Templates) {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

/-- Finite syntactic witnesses for each execution of the scheduled refresh,
in the same alphabet as the shrinking passes. -/
noncomputable def refreshProcedureWitnesses : (B.refreshProcedure f hf).MapWitnesses f := by
  unfold refreshProcedure
  apply Procedure.MapWitnesses.ofPass
  intro g X c v x z
  exact MonomialWitness.right f (dyadicRefreshKernelWitness X S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh S.port_order S.degree_bounds.2
    (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2 c v x z)

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
