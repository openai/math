import OAI.Computability.VPVNP.LiveCompressedPairBranchCharge
import OAI.Computability.VPVNP.PairTerminalQuietHandoff

/-! # The same terminal branch on equal fixed instruction banks

The compressed pair's packed directory is sized at runtime. Reindexing
a chosen branch along the equality of its five worker tables retains the
raw vertex memory and all physical report lists used for accounting.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair.TerminalBranchData

open BurstRAM PairSimulation LocalHistory NetworkKernel TerminalLink

variable {w clk : ℕ} {N : Network} {A : Type*} [CommRing A] {L : Type} [Fintype L]
  {κ : L → A} {arc : ScanPhase N} {sites : SiteParsers κ N} {pub : Fin 11 → Word w} {m : Memory w}
  {old current : TerminalLink.Stage → PairTable}
  (branch : TerminalBranchData old pub clk m arc sites) (same : old = current)

/-- Interpret a chosen physical terminal branch on the equal runtime instruction bank. -/
def reindexWorkers : TerminalBranchData current pub clk m arc sites := same ▸ branch

theorem reindex_bitMemory (x : arc.Path) :
    ((branch.reindexWorkers same).bitPaths x).val.memory = (branch.bitPaths x).val.memory := by
  cases same
  rfl

theorem reindex_vertexMemory (x : TerminalData arc sites) :
    ((branch.reindexWorkers same).vertexPaths x.arcs x.choices).val.memory =
      (branch.vertexPaths x.arcs x.choices).val.memory := by
  cases same
  rfl

theorem reindex_sharedReports (x : TerminalData arc sites) :
    ((branch.reindexWorkers same).chosenTrace x).sharedBits.logs =
      (branch.chosenTrace x).sharedBits.logs := by
  cases same
  rfl

theorem reindex_vertexReports (x : TerminalData arc sites) :
    ((branch.reindexWorkers same).chosenTrace x).vertices.logs =
      (branch.chosenTrace x).vertices.logs := by
  cases same
  rfl

end LiveProgram.CompressedPair.TerminalBranchData

end VPVNP
end Computability
end OAI
