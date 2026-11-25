import OAI.Hierarchy.DescentTerminalCellCoordinates
import OAI.Hierarchy.DescentTerminalClippedFields

namespace OAI
/-! # Count distinct live private references in the genuine sparse terminal home -/
namespace Hierarchy.DescentTerminalVertexFields
open Computability.VPVNP.BurstRAM DescentTerminalSiteShelves
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w groups blocks : ℕ}

def cutFields (x : Key H N A→ℕ) (q : ℕ) : Finset ℕ :=
  (Finset.univ.image (fun ij : Fin N×Fin A=>clean x (nodeArg ij.1 ij.2))).filter (q<·)

def privateHome (data : BlockFields q t H N A w groups blocks) : ℕ :=
  ∑c : Fin (groups*blocks), if blankAt data c≠0 then
    (cutFields (venueField (cellAt data c)) q).card else 0

theorem privateHome_eq (data : BlockFields q t H N A w groups blocks) :
    privateHome data=∑c : Fin (groups*blocks), if blankAt data c≠0 then
      (cutFields (venueField (cellAt data c)) q).card else 0 := rfl

end
end Hierarchy.DescentTerminalVertexFields

end OAI
