import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Labels, registers and slots of a list of physical column scans -/
namespace Hierarchy.DescentTerminalPrimitiveNames
open ProtocolRAM
open DescentStaticWordColumn (names names_seq names_scan)
noncomputable section

/-- Each active source emits one genuine shared-address or host-address instruction stream. -/
def readNames : List Pass → ℕ
  | [] => 0
  | p :: ps => (11 + 4 * p.term.work) + readNames ps

theorem schedule_names (w : ℕ) (ps : List Pass) :
    names (ProtocolRAM.program w ps) = 15 + readNames ps := by
  induction ps with
  | nil => simp only [ProtocolRAM.program, names_scan, readNames]; rfl
  | cons p ps ih =>
    simp only [ProtocolRAM.program, Pass.procedure, names_seq, names_scan, ih, readNames]
    omega

theorem batch_names_le (K out H pitch : ℕ) (e : ℕ → Expr) (work : ∀ j, (e j).work ≤ K)
    (start n : ℕ) :
    readNames (DescentPackedFlowBatch.passes out H pitch e start n) ≤ (11 + 4 * K) * n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [DescentPackedFlowBatch.passes, readNames, Nat.mul_succ]
    have old := ih (start + 1)
    have next := work start
    omega


end
end Hierarchy.DescentTerminalPrimitiveNames

end OAI
