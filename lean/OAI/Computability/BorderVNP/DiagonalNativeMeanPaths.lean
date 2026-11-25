import OAI.Computability.BorderVNP.DiagonalNativeCorePaths
import OAI.Computability.BorderVNP.DiagonalPhysicalMeanOwner
import OAI.Computability.BorderVNP.DiagonalBottomChoices

/-! # Recovered original witnesses and passing paths on the selected native cube placement -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs Diagonal.CellEntries
open scoped Classical

set_option maxHeartbeats 1600000

variable {D C ns ne np n d b h K s exp r : ℕ} {P J Param Gadget Team Hidden A : Type}
    [Fintype P] [Fintype Team] [Fintype Param] [Fintype A] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np) (state : Site.Programs N)
    (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (birthWidth : ∀ j, (state (host j)).birth.work = mult j*(slabs j).stride)
    (teams : Fin (r+1) ≃ Team) (recv : A → Fin C) (w : A → ℕ)
    {eCount : ℕ} (ord : N.CrossingEdge cell ≃ Fin eCount) (cs : List (Fin C)) (nodup : cs.Nodup)
    (cover : cs.toFinset=Finset.univ) (hd : 0<d) (hb : 0<h*b) {W : ℝ} {M : ℕ}
    (budget : PackedLabelBudget N cell recv w W M (d^(n+1)))
    (ports : Ports bits) (number : Gadget ↪ ℕ) (hidden : BottomChoices slabs mult ≃ Hidden)
    (terms : Hidden → Tracked Team Param Gadget exp N)
    (model : ∀ z, TagModels N edgeID portID state (terms (hidden z)).tags number (carryPred host (birthPredicate slabs mult z)))
    (owner : Fin ns → ℕ) (reports : Fin C → List (List ℕ))
    (ho : ∀ v, owner (siteID v)=(cell v).val) (birthLocal : ∀ v, (state v).birth.Local)
    (schema : ∀ v, (state v).program.Schema) (relative : ∀ v, (state v).program.RelativeBoxes)
    (pos : TableEntry n b h K s → Gadget)

local notation3 "packet" => PacketPlacement.ofNativeMean (K:=K) teams s N cell recv w ord cs nodup cover hd hb budget
local notation3 "slot" => meanPackedEmbedding N cell recv w ord cs nodup cover n d hd hb budget
local notation3 "owns" => (fun sel : Packet n d (blocksFor W (h*b) (d^(n+1))) → Selector n K h => greedyOwner r b s (meanPackedLabel N cell recv w cs n d hd) recv w sel)
local notation3 "size" => placedSize N state
local notation3 "Bank" => (c : Fin C) → Fin (externalBase N cell c size) → Bool
local notation3 "checks" => GuardedCores N cell siteID edgeID portID state owns slot ports owner reports

/-- For the exact bins and first-minimum ownership scanned by the native
program, recover the original fine witnesses and the full passing packet path.
The team numbering belongs to the mathematical tensor. The routed payloads
use the actual physical team numbers. -/
noncomputable def nativeMeanCoreEquiv :
    {a : Routed (b:=b) (s:=s) owns × Bank // checks a.1 a.2} ≃
      (Σ z : Hidden, PacketPlacement.Passing packet (terms z) ports pos) := by
  let changeWitness := Equiv.sigmaCongrLeft (β:=fun z : Hidden => PacketPlacement.Passing packet (terms z) ports pos) hidden
  exact (nativeCoreEquiv N cell siteID edgeID portID state host slabs mult birthWidth owns slot ports
    number (fun z => (terms (hidden z)).tags) model owner reports ho birthLocal schema relative (fun _ => pos)).trans changeWitness

local notation3 "decoded" => nativeMeanCoreEquiv N cell siteID edgeID portID state host slabs mult birthWidth teams recv w
  ord cs nodup cover hd hb budget ports number hidden terms model owner reports ho birthLocal schema relative pos

/-- The map reads the actual independent original fine bits from the retained
physical work prefixes, in the selected bottom witness enumeration. -/
theorem nativeMeanCoreEquiv_hidden (a : {a : Routed (b:=b) (s:=s) owns × Bank // checks a.1 a.2}) :
    (decoded a).1 = hidden (extractBottom N cell siteID size owns slabs mult
      (fun _ j => retainedLocation N state host slabs mult birthWidth j) a.val.1 a.val.2) := rfl

/-- The recovered path uses the received payload itself and the actually
guessed private wires of every cell. -/
theorem nativeMeanCoreEquiv_path (a : {a : Routed (b:=b) (s:=s) owns × Bank // checks a.1 a.2}) :
    (decoded a).2.val = rawPath N cell edgeID state owns a.val.1 a.val.2 := rfl

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
