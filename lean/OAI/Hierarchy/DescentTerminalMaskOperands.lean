import OAI.Hierarchy.DescentTerminalCellCoordinates
import OAI.Hierarchy.DescentTerminalMaskChannels
import OAI.Hierarchy.DescentPackedCensusPins

namespace OAI
/-! # Native rectangular operand arrays supply each scalar's authentic numerical primitive -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentSIMDLookup DescentSixParty.PackedCensus
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical Fin.CommRing
noncomputable section
variable {q t H N A w groups blocks shops wb : ℕ}
local notation "sized" => familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)
local notation "Fields" => PrimitiveFields q t H N A w
local notation "dataAt" => measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups)

/-- One earlier physical word per common host and (old block, family). Reads of
multiple occurrences of the same public operand naturally retain the same integer. -/
theorem operand_field (machine : MaskedShelf blocks) (m : Memory wb) (positive : 0<groups)
    (v : Fin shops→Fin groups→Fin blocks→Fields)
    (capacity : ∀f,sized f*groups≤wb)
    (ready : ∀(b:Fin blocks) (f:Fin 8) (i:Fin shops),(machine.channel (finProdFinEquiv (b,f.succ))).read m (i.val:Word wb)=
      ((data (fun i g=>panelWord (v i g b) f) (i,onlyBatch positive)).val:Word wb))
    (i : Fin shops) (g : Fin groups) (b : Fin blocks) (k : Key H N A) :
    venueField (q:=q) (t:=t) (w:=w) (cellAt (dataAt machine m i) (finProdFinEquiv (g,b))) k =
      (v i g b (group k) (item k)).val := by
  have eqn : cellAt (dataAt machine m i) (finProdFinEquiv (g,b)) = panelWord (v i g b) := by
    funext f
    exact from_cell (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) machine m positive b f
      (fun host lane => panelWord (v host lane b) f) (capacity f) (ready b f) i g
  rw [eqn]
  exact panelField (v i g b) k

end
end Hierarchy.DescentTerminalVertexFields

end OAI
