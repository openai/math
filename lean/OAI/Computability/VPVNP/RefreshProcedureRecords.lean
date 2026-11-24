import OAI.Computability.VPVNP.RefreshHistory
import OAI.Computability.VPVNP.RefreshProcedure
import OAI.Computability.VPVNP.CompressionProcedureHistory

/-!
# Uniform record bounds for the scheduled expander refresh

The actual refresh in a compression block has one substep. Its local resource
constant depends only on the chosen degrees, expander and fixed motif template.
It can therefore be fixed before specializing the parameter values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open MotifConversion Refresh DegreeRefresh

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Uniform count and growth constant for the refresh in this schedule. -/
noncomputable def refreshRecordConstant : ℕ :=
  max (refreshExtraCount S.portExponent (2 ^ S.expanderExponent) +
    1 * (2 * 2 ^ S.portExponent) + 2 * 2 ^ S.degreeExponent 0 + 1)
    (refreshLengthConstant S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
      B.refresh + 1)

variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

/-- All branches of the scheduled refresh retain the actual port records and satisfy
one bound, independent of the specialization ring, lane count and input widths. -/
noncomputable def refreshProcedureRecords :
    (B.refreshProcedure f hf).RecordBounds B.refreshRecordConstant 1 := by
  let hdH := Nat.two_pow_pos S.expanderExponent
  let conn := (S.port_bound.connected_and_pos S.port_order).1
  let hd := S.degree_bounds.2
  let hk := ((B.solution_iff f).mp hf).2
  unfold refreshProcedure
  refine Procedure.RecordBounds.ofPass _ _ _ _ _ _ (fun _ X =>
    let pass := dyadicRefreshPass X S.graph hdH conn B.refresh S.port_order hd (f ∘ Sum.inr) hk
    pass.slotRecords (refreshLocalRecords X S.graph hdH conn B.refresh S.port_order hd (f ∘ Sum.inr) hk)) ?_
  intro g X
  exact refreshPass_records_bounded X S.graph hdH conn B.refresh S.port_order hd (f ∘ Sum.inr) hk
    (by linarith [S.portComparison_pos])

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
