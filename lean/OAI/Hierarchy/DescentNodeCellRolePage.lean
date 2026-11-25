import OAI.Hierarchy.DescentOriginalPaddedNodes
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # The original node labels in a single padded physical row -/
namespace Hierarchy.DescentSixParty.Reached.NodeCells
open DescentKernelHistory DescentLocalArchiveOrder DescentColonies DescentCompiler DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist : ℕ}
  (cap : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W) (ord : Local B)
  {H N a : ℕ} (label : NodeOrder.All B→Cell a)
def rolePage (x : Block k) (h : Fin H) (g : Fin (S.groupCount age)):Cell (a*N):=
  encode a N (fun j=>(atPhysical cap B ord x j h g).elim 0 label)

end
end Hierarchy.DescentSixParty.Reached.NodeCells

end OAI
