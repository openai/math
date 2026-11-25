import OAI.Computability.BorderVNP.DiagonalTaggedPrivateCells
import OAI.Computability.BorderVNP.DiagonalPhysicalPassGuard

/-! # Reading a full mathematical cube path directly from physical private cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.Inherited Packing.Inherited.Placement Diagonal.CellEntries
open Scatter.Assignment
open private wire_ends supplied_at from OAI.Computability.BorderVNP.PackedInheritedMergedEnds
open scoped Classical

variable {D ns ne np n d blocks b h K s : ℕ} {P Cell Team : Type} [Fintype P] [DecidableEq Cell]
    {bits' : P → ℕ} (N : Network D P bits') (cell : N.Site → Cell)
    (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np) (state : Site.Programs N)
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (bank : Ports bits')
    (q : Routed (b:=b) (s:=s) owners)

local notation3 "size" => placedSize N state

/-- The physical cube path obtained before checking any staging or
reports. It reads exactly the real within-cell cables and routed bits. -/
noncomputable def rawPath (raw : (c : Cell) → Fin (externalBase N cell c (placedSize N state)) → Bool) :
    Path N cell n d blocks b h K s :=
  (adaptivePathEquiv N cell n d blocks b h K s owners).symm
    (fun c => guessedWords N cell c edgeID (privateWires N cell size c (raw c)),q)

/-- The independent two endpoint words provided by one distributed
assignment at the selected public packed slots. -/
def routedEnds (direction : Bool) (i : LiveBit N cell) : Bool :=
  let z := (payloadEquiv (D:=D) q.1).symm (lookup q.2)
  readEnd z.1 z.2.1 direction (slot i)

/-- The actual per-cell logical supply vector in sorted physical ordinal
order, including its independent source and destination ends. -/
noncomputable def pathSupply (c : Cell) : Fin (suppliedSize N cell c) → Bool :=
  endSupply N cell c edgeID portID bank (routedEnds N cell owners slot q)

/-- Every private or supplied cable digit in the candidate cell is the
corresponding factor input of the decoded full path, even when two
different ends of an opened wire carry different bits. -/
theorem localWire_path (raw : (c : Cell) → Fin (externalBase N cell c (placedSize N state)) → Bool)
    (c : Cell) (v : {v : N.Site // cell v=c}) :
    localWire N cell edgeID portID owners (pathSupply N cell edgeID portID owners slot bank) q c
      (privateWires N cell size c (raw c)) v = pathEdges slot (rawPath N cell edgeID state owners q raw) v.val := by
  let old := fun v : N.Site => (state v).program
  let g := fun c => privateWires N cell size c (raw c)
  let prior : RawWork N cell old := fun c => Fin.append (g c) (fun _ => false)
  have prefixEq (c : Cell) : privateWires N cell (fun v => (old v).work) c (prior c) = g c := by
    funext i
    exact Fin.append_left _ _ i
  have interior : insideOfRaw N cell edgeID old prior = fun c => guessedWords N cell c edgeID (g c) := by
    funext c
    exact congrArg (guessedWords N cell c edgeID) (prefixEq c)
  funext e j
  have hw := wire_ends N cell c edgeID portID old bank (routedEnds N cell owners slot q) prior v e j
  change (wire N cell c edgeID portID v e j).elim (privateWires N cell (fun u => (old u).work) c (prior c))
      (pathSupply N cell edgeID portID owners slot bank q c) =
    siteWord N cell v.val e (insideOfRaw N cell edgeID old prior) (routedEnds N cell owners slot q) j at hw
  rw [prefixEq,interior] at hw
  exact hw

/-- Every supplied exterior bit of this site's sparse table agrees with
the separately delivered free-group word used in the tagged expansion. -/
theorem localPort_path (c : Cell) (v : {v : N.Site // cell v=c}) :
    localPort N cell edgeID portID owners (pathSupply N cell edgeID portID owners slot bank) q c v =
      fun (p : Attached N v.val) => bank p.val := by
  funext p j
  exact supplied_at N cell c edgeID portID bank (routedEnds N cell owners slot q)
    (.inr ⟨p.val,(congrArg cell p.property).trans v.property⟩) j

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
