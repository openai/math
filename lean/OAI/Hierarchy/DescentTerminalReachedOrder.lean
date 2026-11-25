import OAI.Hierarchy.DescentReachedOccurrence
import OAI.Hierarchy.DescentReached
import OAI.Hierarchy.DescentTerminalCableOrder

namespace OAI
/-! # Fixed common terminal positions and the actual occurrence calendar at a position -/
namespace Hierarchy.DescentSixParty.Reached
open DescentCompiler DescentHostDegree DescentHostDirectory DescentColonies
open DescentTerminalGraphPositions DescentTerminalCableOrder
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits}
    {G:PoweredGadget F} {price ε:ℝ} {S:AtomSchedule} {k age z degree wire hist : ℕ}
    (R:Reached W G price ε S k age z degree wire hist)

/-- Physical endpoint chronology orders the common neighbor ports for both copies
of an internal ribbon; the terminal-table rows use the reached site chronology. -/
def terminalOrder [Fintype P] (p:ℕ) (exterior:P↪ℕ)
    (args : ∀v,DescentKernelHistory.Boundary W.graph v↪ℕ) : Order W.graph (S.hostSize age) p :=
  DescentTerminalCableOrder.order W.graph R.home R.order p exterior
    ((R.placement.site R.vertex R.valid.coordinates).trans ⟨Fin.val,Fin.val_injective⟩) args

end
end Hierarchy.DescentSixParty.Reached

end OAI
