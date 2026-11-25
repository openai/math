import OAI.Computability.BorderVNP.DiagonalPinnedGuards

/-! # Shared physical coordinates for a signed column on a fixed public history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.Inherited
open scoped Classical

/-- The private sites, rows, live slots, and team scheduler shared by the
public preparation and the path decoder. A concrete signed history computes
all fields from its retained rows and its physical packet. -/
structure CoreDirectory {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (n d blocks b h K r : ℕ) where
  /-- Public reduced cells, including empty cells. -/
  cells : ℕ
  /-- Padded row directories of the terminal machine. -/
  siteRows : ℕ
  /-- Padded number of cable directory entries. -/
  edgeRows : ℕ
  /-- Padded number of external word identifiers. -/
  portRows : ℕ
  /-- Cell ordinal of each present site. -/
  cell : N.Site → Fin cells
  /-- Public sparse names of each present site, cable and external word. -/
  siteID : N.Site ↪ Fin siteRows
  /-- Address of a retained cable. -/
  edgeID : N.Edge ↪ Fin edgeRows
  /-- Address of a placed external word. -/
  portID : P ↪ Fin portRows
  /-- Actual private program, including retained original work ranges. -/
  programs : Site.Programs N
  /-- Team charged for each group on the chosen selectors. -/
  owners : (Packet n d blocks → Selector n K h) → Fin d → Fin (r+1)
  /-- Occupied live slots in the publicly allocated padded block rectangle. -/
  slot : LiveBit N cell ↪ Slot n d blocks (h*b)

namespace CoreDirectory

variable {D n d blocks b h K r : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
    (B : CoreDirectory N n d blocks b h K r)

/-- The routed cube bits after the two actual endpoint padding tests. -/
abbrev Route (symbols : ℕ) := {u : Routed (b:=b) (s:=symbols) B.owners // RoutedPins N B.cell B.owners B.slot u}

/-- Arbitrary guessed original wires and proposed retained work bits before the cell checks. -/
abbrev Bank := (c : Fin B.cells) → Fin (externalBase N B.cell c (placedSize N B.programs)) → Bool

/-- Read owners on occupied sparse rows. Empty row addresses have no private cells. -/
noncomputable def owner (i : Fin B.siteRows) : ℕ := ((Function.partialInv B.siteID i).map (fun v => (B.cell v).val)).getD 0

@[simp] theorem owner_site (v : N.Site) : B.owner (B.siteID v) = (B.cell v).val := by
  simp [owner,Function.partialInv_left B.siteID.injective]

/-- At a fixed raw pin the guard tests the routed endpoint bits and each
original ordered factor check on the same local bank. The report count
addresses enter when a returning report is checked against its observations. -/
def Guard {symbols : ℕ} (pin : Ports bits) (x : B.Route symbols × B.Bank) : Prop :=
  GuardedCores N B.cell B.siteID B.edgeID B.portID B.programs B.owners B.slot pin B.owner (fun _ => []) x.1.val x.2

end CoreDirectory
end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
