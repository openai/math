import OAI.Computability.VPVNP.PairTerminalPackedBudget
import OAI.Computability.VPVNP.PairVertexGeometrySegment
import OAI.Computability.VPVNP.PairSimulationLeafRole
import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherCode

/-!
# Fixed terminal code with the live leaf and endpoint registers

The descriptor bootstrap, width scan, traversal controller and shared-bit
worker precede a single vertex image. Its geometry segment reconstructs the
argument, histogram, cache and interpreter addresses from the eleven public
operands. The root gather reads both endpoints, and the cursor leaf executes
the virtual coefficient machine. The two map segments occupy the remaining
role entries of that same image.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM PrivateRAM Compression CompressorRecords LiveProgram

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

/-- The register-sharing segments of the physical per-vertex burst. -/
noncomputable def installedSegments (c : Constants) (S : BlockSchedule k) (p q : ℕ)
    (shrink refresh : VertexImage.Segment) : VertexImage.Part → VertexImage.Segment :=
  VertexImage.segments (VertexGeometry.segment c (slotDegree S) p q)
    TerminalRootGather.segment LeafRole.segment shrink refresh

/-- All opcodes and register counts are fixed before the length, coefficient
assignment and selected branches. -/
noncomputable def installedTable (B : S.Templates) (c : Constants) (p q : ℕ)
    (shrink refresh : VertexImage.Segment) : PairTable :=
  table (BlockProgram.allocationShape B) B.recordLimit (installedSegments c S p q shrink refresh)

/-- The exact same instruction bank executes against the packed chronological
directory emitted at any length by the calendar. -/
theorem installed_at_layout (B : S.Templates) (c : Constants) (p q base positions blocks : ℕ)
    (shrink refresh : VertexImage.Segment) :
    table (BlockProgram.layout B base positions blocks).shape B.recordLimit
      (installedSegments c S p q shrink refresh) = installedTable B c p q shrink refresh :=
  congrArg TerminalLink.table (TerminalLayout.packed_workers B base positions blocks _)

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
