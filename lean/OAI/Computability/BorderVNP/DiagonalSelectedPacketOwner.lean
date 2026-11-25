import OAI.Computability.BorderVNP.DiagonalNativeDemandCore

/-! # Native report ownership for the selected packet and its original sparse directory -/

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

/-- The directory and packet use the same delivery ordinal and the same
conditional-mean labels. The packet labels can therefore be used directly
with a declaration read back at one candidate's entry. -/
theorem checkedDirectory_packetOwners {Team : Type} (teams : Fin (r+1) ≃ Team)
    (budget : PackedLabelBudget N cell recv cost volume cap (d^(cube.pred+1))) :
    let selected := checkedDirectory (r:=r) N cell site edge port state dir old live gap bounds cube hd budget
    let labels := (packet N cell edge port dir old live gap bounds cube teams hd budget).label
    selected.owners=(greedyOwner r cube.b cube.width labels recv cost) := rfl

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
