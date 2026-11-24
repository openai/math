import OAI.Computability.VPVNP.PairTerminalVertexBank
import OAI.Computability.VPVNP.PairShrinkVertexImage
import OAI.Computability.VPVNP.PairRefreshVertexRun

/-!
# The complete fixed opcode table for a compressed pair's terminal phase

The same parameter numbering is used in every shrinking matrix and every
refresh matrix. The refresh tie and slice ordering comes from the actual
block planner. All five terminal workers share the eleven public operands of
the enclosing pair. Their finite instruction and register counts depend only
on the schedule, the fixed live constants and the label enumeration.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open Compression CompressorRecords LiveProgram

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable (c : Constants) (p q : ℕ) {labels : ℕ} (order : B.Entry ≃ Fin labels)

/-- The actual map, leaf, shared-wire, geometry and DFS segments on one
fixed register allocation. -/
noncomputable def nativeSegments : VertexImage.Part → VertexImage.Segment :=
  installedSegments c S p q (ShrinkVertexImage.shrinkSegment B order)
    (RefreshVertex.refreshSegment B (RefreshBlockPlan.order B)
      (RefreshBlockPlan.shape B).stride order)

/-- The input-independent terminal table in the paper's live pair machine. -/
noncomputable def nativeTable : PairTable :=
  table (BlockProgram.allocationShape B) B.recordLimit (nativeSegments B c p q order)

/-- Its instruction image is the actual five-stage program for each packed
level directory, with the concrete finite role handlers installed. -/
theorem nativeTable_eq (base positions blocks : ℕ) :
    table (BlockProgram.layout B base positions blocks).shape B.recordLimit
      (nativeSegments B c p q order) = nativeTable B c p q order :=
  congrArg TerminalLink.table (TerminalLayout.packed_workers B base positions blocks _)

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
