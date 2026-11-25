import OAI.Computability.BorderVNP.DiagonalNativeCoreDirectory
import OAI.Computability.BorderVNP.PackedNativeDemandPacket

/-! # Private coordinates selected by the same directory as the signed packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing Diagonal Diagonal.CellEntries BorderVNP.Cube Cube.Physical NativeAssignments Packing.Inherited
open scoped Classical

variable {D C sv ne np r : ℕ} {P K : Type} [Fintype P] [Field K] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (site : N.Site ↪ Fin sv)
    (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np) (state : Site.Programs N)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site)
    (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (gap : ℕ) (bounds : dir.DestinationBounds) (cube : FixedCube K)
    {d : ℕ} (hd : 0<d) {volume : ℝ} {cap : ℕ}

local notation "list" => rows N cell edge port dir old live gap
local notation "recv" => receiver N cell edge port dir old live gap bounds
local notation3 (prettyPrint := false) "cost" => fun i : Fin (list).length => (list)[i.val].width

/-- All private call indices on the native packet. The prefix scan of the
actual delivery rows determines both the padded slots and greedy owners. -/
noncomputable def checkedDirectory
    (budget : PackedLabelBudget N cell recv cost volume cap (d^(cube.pred+1))) :
    CoreDirectory N cube.pred d (blocksFor volume (cube.h*cube.b) (d^(cube.pred+1))) cube.b cube.h cube.copies r where
  cells := C
  siteRows := sv
  edgeRows := ne
  portRows := np
  cell := cell
  siteID := site
  edgeID := edge
  portID := port
  programs := state
  owners := greedyOwner r cube.b cube.width (meanPackedLabel N cell recv cost (List.finRange C) cube.pred d hd) recv cost
  slot := meanPackedEmbedding N cell recv cost (cableOrder N cell edge) (List.finRange C)
    (List.nodup_finRange C) (by ext; simp) cube.pred d hd cube.block_pos budget

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
