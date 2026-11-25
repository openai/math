import OAI.Computability.BorderVNP.DiagonalNativeDemandCore

/-! # The native cube report uses the selected history's directed crossing slots -/

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

/-- A physical host table can prove the cable capacity independently. The resulting
within-bin addresses are exactly the bits used by the native signed packet. -/
theorem checkedDirectory_host_slot (budget : PackedLabelBudget N cell recv cost volume cap (d^(cube.pred+1)))
    (size : ∀ j, load (cablePair (cableOrder N cell edge) (crossSrc N cell) (crossDst N cell)
      (meanPackedLabel N cell recv cost (List.finRange C) cube.pred d hd))
      (crossWidth N cell ∘ (cableOrder N cell edge).symm) j ≤
        blocksFor volume (cube.h*cube.b) (d^(cube.pred+1))*(cube.h*cube.b)) :
    packedSlotEmbedding N cell (cableOrder N cell edge)
      (meanPackedLabel N cell recv cost (List.finRange C) cube.pred d hd)
      (blocksFor volume (cube.h*cube.b) (d^(cube.pred+1))) (cube.h*cube.b) size =
    (checkedDirectory (r:=r) N cell site edge port state dir old live gap bounds cube hd budget).slot := by
  unfold checkedDirectory meanPackedEmbedding balancedPackedEmbedding
  rfl

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
