import OAI.Computability.BorderVNP.PackedNativeDemandLabels
import OAI.Computability.BorderVNP.DiagonalFixedCube

/-! # The signed physical packet for the numbered cell and cable directories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing Diagonal Diagonal.CellEntries BorderVNP.Cube Cube.Physical
open scoped Classical

variable {D C ne np r : ℕ} {P Team K : Type} [Fintype P] [Field K] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (gap : ℕ) (bounds : dir.DestinationBounds)
    (cube : FixedCube K) (teams : Fin (r+1) ≃ Team) {d : ℕ} (hd : 0<d) {volume : ℝ} {cap : ℕ}

local notation "list" => rows N cell edge port dir old live gap
local notation "recv" => receiver N cell edge port dir old live gap bounds
local notation3 (prettyPrint := false) "cost" => fun i : Fin (list).length => (list)[i.val].width

/-- The selected packet uses physical sparse-cable order and the native ascending
cell scan. Its greedy scheduling sees exactly the certified delivery list. -/
noncomputable def packet
    (budget : PackedLabelBudget N cell recv cost volume cap (d^(cube.pred+1))) :
    PacketPlacement Team cube.pred d cube.b cube.h cube.copies N :=
  PacketPlacement.ofNativeMean teams cube.width N cell recv cost (cableOrder N cell edge)
    (List.finRange C) (List.nodup_finRange _) (by ext; simp) hd cube.block_pos budget

/-- Deterministic native team stored for every selector and every group
of the common signed packet, including groups with zero outgoing volume. -/
theorem packet_owner (budget : PackedLabelBudget N cell recv cost volume cap (d^(cube.pred+1)))
    (sel : Packet cube.pred d (blocksFor volume (cube.h*cube.b) (d^(cube.pred+1))) →
      Selector cube.pred cube.copies cube.h) (g : Fin d) :
    teams.symm ((packet N cell edge port dir old live gap bounds cube teams hd budget).team sel g) =
      greedyOwner r cube.b cube.width (meanPackedLabel N cell recv cost (List.finRange C) cube.pred d hd)
        recv cost sel g :=
  teams.symm_apply_apply _

/-- The physical scheduler writes the owner of the packet selected on this
same published geometry, for the actual passing length declaration. -/
theorem packet_owner_stored {l : GroupWeights.Layout} {tl : TeamNative.Layout}
    (teamOrder : Fin (tl.r+1) ≃ Team) (positive : 0<l.groups)
    (budget : PackedLabelBudget N cell recv cost volume cap (l.groups^(cube.pred+1)))
    (ids : Fin C ≃ Fin l.cells) {before after : ℕ → ℕ}
    (scheduled : GroupWeights.ScheduleResult l tl before after)
    (sel : Packet cube.pred l.groups (blocksFor volume (cube.h*cube.b) (l.groups^(cube.pred+1))) →
      Selector cube.pred cube.copies cube.h)
    {decl : LengthDeclaration cube.pred l.groups} (accepted : passesLengths cube.b cube.width sel decl)
    (image : GroupWeights.PhysicalImage l before (blocksFor volume (cube.h*cube.b) (l.groups^(cube.pred+1)))
      cube.b cube.copies cube.h decl (meanPackedLabel N cell recv cost (List.finRange C) cube.pred l.groups positive ∘ ids.symm)
      (ids ∘ recv) cost) (g : Fin l.groups) :
    after (tl.owners+g.val) =
      (teamOrder.symm ((packet N cell edge port dir old live gap bounds cube teamOrder positive budget).team sel g)).val :=
  PacketPlacement.ofNativeMean_owner_stored teamOrder cube.width N cell recv cost ids (cableOrder N cell edge)
    (List.finRange C) (List.nodup_finRange _) (by ext; simp) positive cube.block_pos budget scheduled sel accepted image g

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
