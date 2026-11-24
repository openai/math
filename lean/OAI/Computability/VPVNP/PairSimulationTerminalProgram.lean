import OAI.Computability.VPVNP.PairSimulationTerminalFive
import OAI.Computability.VPVNP.PairTraversalTerminalBootstrap
import OAI.Computability.VPVNP.PairTerminalPrefixWorker
import OAI.Computability.VPVNP.PairTraversalControllerCode
import OAI.Computability.VPVNP.PairSimulationFinalBitWorker
import OAI.Computability.VPVNP.PairVertexSiteSegments

/-!
# Terminal program of the compressed pair

The first four stages are the actual metadata, prefix, traversal-row and
shared-bit tables. The final stage is the numerical image of the finite
vertex segments, with its ordinal guard and return table. The program has
the eleven public words of the enclosing compressed pair.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM PrivateRAM CompressorRecords TerminalLink
open LiveProgram (PairTable)

set_option maxRecDepth 4096

private def pack {p r : ℕ} (t : Template p r 11) : PairTable := ⟨p,r,t⟩

variable (F : DescriptorSpace.Shape) (limit : ℕ) (S : VertexImage.Part → VertexImage.Segment)

/-- Static opcode tables in the physical order of execution. -/
noncomputable def workers : Stage → PairTable :=
  ![pack (TerminalBootstrap.table F limit), pack TerminalPrefix.Worker.table,
    pack TraversalController.Native.table, pack FinalBits.Worker.table, pack (VertexImage.template S)]

/-- The fixed terminal program linking metadata, scans, traversal rows and vertex code. -/
noncomputable def table : PairTable := TerminalLink.table (workers F limit S)

theorem bootstrap_table : workers F limit S Stage.bootstrap = pack (TerminalBootstrap.table F limit) := rfl
theorem prefix_table : workers F limit S Stage.prefixRows = pack TerminalPrefix.Worker.table := rfl
theorem row_table : workers F limit S Stage.traversalRows = pack TraversalController.Native.table := rfl
theorem shared_table : workers F limit S Stage.sharedBits = pack FinalBits.Worker.table := rfl
theorem vertex_table : workers F limit S Stage.vertices = pack (VertexImage.template S) := rfl

/-- The physical instruction image with the actual two endpoint guards and
bootstrap/return segments, parametrized only by the five remaining vertex
code segments installed in the role dispatcher. -/
noncomputable def siteProgram (geometry rootFields leaf shrink refresh : VertexImage.Segment) : PairTable :=
  table F limit (VertexImage.segments geometry rootFields leaf shrink refresh)

variable {w : ℕ} (pub : Fin 11 → Word w) (cap : ℕ)

/-- Full forward and reverse semantics, preserving the user's arbitrary cap
on the native reports and the exact branch strings of the five-stage table. -/
theorem accepts_iff (m : Memory w) (bs : List (List Bool)) (ok : List (Report w) → Prop)
    (fit : 32 ≤ 2^w) (hcap : 26 ≤ cap) :
    (∃ rs, runSegment (((table F limit S).table.instantiate w pub).program) cap (some 0) m bs = some rs ∧
      endState (some 0) rs = none ∧ ok rs) ↔
      ∃ ls, Visits (workers F limit S) pub cap (some .initial) m bs ls ∧ finish (some .initial) ls = none ∧
        ok (reports (header pub) ls) :=
  actual_iff (workers F limit S) pub cap m bs ok fit hcap

/-- An accepting terminal path contains one completed phase for each of
the five actual workers, in the table's physical order. -/
theorem accepts_five (m : Memory w) (bs : List (List Bool)) (ok : List (Report w) → Prop)
    (fit : 32 ≤ 2^w) (hcap : 26 ≤ cap) :
    (∃ rs, runSegment (((table F limit S).table.instantiate w pub).program) cap (some 0) m bs = some rs ∧
      endState (some 0) rs = none ∧ ok rs) ↔
      ∃ t : FiveTrace (workers F limit S) pub cap m, bs = t.choices ∧ ok (reports (header pub) t.logs) :=
  TerminalLink.accepts_five (workers F limit S) pub cap m bs ok fit hcap

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
