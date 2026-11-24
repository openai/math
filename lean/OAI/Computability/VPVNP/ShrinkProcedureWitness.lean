import OAI.Computability.VPVNP.ShrinkStateWitness
import OAI.Computability.VPVNP.ShrinkProcedure
import OAI.Computability.VPVNP.CompressionMonomialHistory

/-!
# The scheduled shrinking procedure in the common parameter alphabet

Shrinking maps use the first group of labels of the two fixed templates.
The scheduled procedure retains every local hidden-field choice and every
map witness for any input network and any number of remaining lanes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open NetworkKernel

variable {k : Type*} [Field k] {S : BlockSchedule k}
variable (B : S.Templates) {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable (i : Fin S.steps)

/-- The shrinking map at the scheduled degree contributes its parameter
multiplicities in the shrinking summand of the common alphabet. -/
noncomputable def shrinkPassWitnesses {g n : ℕ}
    (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) : (B.shrinkPassAt f hf i h X).MapWitnesses f := by
  subst n
  intro sel v x z
  exact MonomialWitness.left f (X.shrinkStateKernelWitness B.shrink (f ∘ Sum.inl)
    ((B.solution_iff f).mp hf).1 (S.shrink i) sel v x z)

set_option maxHeartbeats 1200000 in
-- Elaborating the dependent input lane equality unfolds the concrete shrinking pass.
/-- All executions of a scheduled shrinking procedure have the concrete
finite parameter witnesses of their selected kernels. -/
noncomputable def shrinkProcedureWitnesses : (B.shrinkProcedure f hf i).MapWitnesses f := by
  exact Procedure.MapWitnesses.ofPass (by unfold packingFactor; positivity)
    shrink_constants.2.2.2.2.2.1.le (le_max_left 0 _)
    (fun g X ↦ B.shrinkPassAt f hf i (packingLaneBits_add _ g) X)
    (fun g X ↦ B.shrinkPassAt_positions f hf i (packingLaneBits_add _ g) X)
    (fun g X ↦ B.shrinkPassAt_energy f hf i (packingLaneBits_add _ g) X)
    (fun g X ↦ B.shrinkPassWitnesses f hf i (packingLaneBits_add _ g) X)

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
