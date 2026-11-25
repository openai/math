import OAI.Computability.BorderVNP.CubePhysicalNumberedPlacement
import OAI.Computability.BorderVNP.DiagonalDirectoryGuardedPaths
import OAI.Computability.BorderVNP.DiagonalNativeDemandCore

/-! # Recovering a numbered packet subtotal from the routed path and its owners -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.PacketPlacement

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical
open scoped Classical

variable {D n d b h K s B T H U : ℕ} {P Team Param Gadget : Type}
    {bits : P → ℕ} {N : Network D P bits} [Fintype Team] [Fintype Param]

/-- Reading the same path and the same team for each group suffices to
recover every entry of the numbered, current-owner subtotal. -/
theorem read_nativeRow (packet : PacketPlacement Team n d b h K N) (t : Tracked Team Param Gadget B N)
    (x : Ports bits) (pos : TableEntry n b h K s → Gadget) (u : packet.Passing t x pos)
    (team : Team ≃ Fin T) (param : Param ≃ Fin H) (scalar : Gadget ≃ Fin U)
    (a : Path N packet.cell n d packet.blocks b h K s) (owners : Fin d → Fin T)
    (path : u.val = a) (assigned : team ∘ packet.team a.2.2.2.1 = owners) :
    physicalRow packet.slot (numberTables param scalar t.tags) x (fun _ => scalar ∘ pos)
      (t.words.number team param scalar) packet.label owners a = packet.nativeRow t x pos u team param scalar := by
  rw [nativeRow, path, assigned]

end Diagonal.CellEntries.PacketPlacement


namespace Cube.Physical.NativeAssignments.CoreDirectory

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs Diagonal.CellEntries
open scoped Classical

variable {D n d blocks b h K s r w H U : ℕ} {P J Team Param Gadget Hidden : Type}
    [Fintype P] [Fintype Team] [Fintype Param] {bits : P → ℕ} {N : Network D P bits}

/-- Counts computed from the independent work bits and cube path in the
receiver's original routed input, with the team assignment of that input. -/
noncomputable def recoveredRow (B : CoreDirectory N n d blocks b h K r)
    (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (widths : ∀ j, (B.programs (host j)).birth.work = mult j*(slabs j).stride)
    (hidden : BottomChoices slabs mult ≃ Hidden) (source : Hidden → Tracked Team Param Gadget w N)
    (x : Ports bits) (pos : TableEntry n b h K s → Gadget) (label : Fin B.cells → Label (n+1) d)
    (team : Team ≃ Fin (r+1)) (param : Param ≃ Fin H) (scalar : Gadget ≃ Fin U)
    (v : B.Route s × B.Bank) : Fin (r+1) → Fin (H+U) → ℕ :=
  let z := hidden (extractBottom N B.cell B.siteID (placedSize N B.programs) B.owners slabs mult
    (fun _ j => retainedLocation N B.programs host slabs mult widths j) v.1.val v.2)
  let path := rawPath N B.cell B.edgeID B.programs B.owners v.1.val v.2
  physicalRow B.slot (numberTables param scalar (source z).tags) x (fun _ => scalar ∘ pos)
    ((source z).words.number team param scalar) label (B.owners v.1.val.1) path

/-- The two coordinates recovered by the guard determine both the scalar
and the parameter subtotal of each individual receiver. -/
theorem recoveredRow_of_read (B : CoreDirectory N n d blocks b h K r)
    (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (widths : ∀ j, (B.programs (host j)).birth.work = mult j*(slabs j).stride)
    (hidden : BottomChoices slabs mult ≃ Hidden) (source : Hidden → Tracked Team Param Gadget w N)
    (x : Ports bits) (pos : TableEntry n b h K s → Gadget) (label : Fin B.cells → Label (n+1) d)
    (team : Team ≃ Fin (r+1)) (param : Param ≃ Fin H) (scalar : Gadget ≃ Fin U)
    (v : B.Route s × B.Bank)
    (z : Hidden) (a : Path N B.cell n d blocks b h K s)
    (read : B.Reads host slabs mult widths hidden v z a) :
    B.recoveredRow host slabs mult widths hidden source x pos label team param scalar v =
    physicalRow B.slot (numberTables param scalar (source z).tags) x (fun _ => scalar ∘ pos)
      ((source z).words.number team param scalar) label (B.owners a.2.2.2.1) a := by
  obtain ⟨hz, ha⟩ := read
  subst z a
  rfl

/-- The packet placement in original batch indices represented by a
native directory with this scalar-label table and team numbering. -/
noncomputable def packetView (B : CoreDirectory N n d blocks b h K r) (label : Fin B.cells → Label (n+1) d)
    (team : Team ≃ Fin (r+1)) : PacketPlacement Team n d b h K N where
  Cell := Fin B.cells
  cell := B.cell
  blocks := blocks
  slot := B.slot
  label := label
  team := fun sel g => team.symm (B.owners sel g)

/-- Transport a returned private read to the original packet's row. Taking
the equality of placements first keeps all dependent path coordinates on
the same cell set and occupied-slot embedding. -/
theorem recoveredRow_on_packet (B : CoreDirectory N n d blocks b h K r)
    (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (widths : ∀ j, (B.programs (host j)).birth.work = mult j*(slabs j).stride)
    (hidden : BottomChoices slabs mult ≃ Hidden) (source : Hidden → Tracked Team Param Gadget w N)
    (x : Ports bits) (pos : TableEntry n b h K s → Gadget) (label : Fin B.cells → Label (n+1) d)
    (team : Team ≃ Fin (r+1)) (param : Param ≃ Fin H) (scalar : Gadget ≃ Fin U)
    (v : B.Route s × B.Bank) (packet : PacketPlacement Team n d b h K N) (same : packet = B.packetView label team)
    (z : Hidden) (u : packet.Passing (source z) x pos)
    (presentation : B.Passing (source z).tags x pos = packet.Passing (source z) x pos)
    (read : B.Reads host slabs mult widths hidden v z ((Equiv.cast presentation).symm u).val) :
    B.recoveredRow host slabs mult widths hidden source x pos label team param scalar v =
      packet.nativeRow (source z) x pos u team param scalar := by
  subst packet
  let a := ((Equiv.cast presentation).symm u).val
  refine (B.recoveredRow_of_read host slabs mult widths hidden source x pos label team param scalar v z a read).trans ?_
  refine (B.packetView label team).read_nativeRow (source z) x pos u team param scalar a (B.owners a.2.2.2.1) rfl ?_
  exact funext fun g => team.apply_symm_apply _

end Cube.Physical.NativeAssignments.CoreDirectory

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

/-- The layout used by the original tagged expansion is exactly the native
directory's occupied slots, scan labels, and transported greedy teams. -/
theorem packet_eq_directoryView {Team : Type}
    (budget : PackedLabelBudget N cell recv cost volume cap (d^(cube.pred+1)))
    (team : Team ≃ Fin (r+1)) :
    let placed := packet N cell edge port dir old live gap bounds cube team.symm hd budget
    placed = (checkedDirectory (r:=r) N cell site edge port state dir old live gap bounds cube hd budget).packetView
      placed.label team := rfl

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
