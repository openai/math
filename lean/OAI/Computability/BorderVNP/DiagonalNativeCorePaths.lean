import OAI.Computability.BorderVNP.DiagonalPrivateCoreEquiv
import OAI.Computability.BorderVNP.DiagonalTaggedNativeCellGuard

/-! # Bijection between actual guarded private cores and the tagged cube paths -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs Diagonal.CellEntries CellSparse
open scoped Classical

set_option maxHeartbeats 1600000

variable {D C ns ne np n d blocks b h K s : ℕ} {P J Param Gadget Team : Type} [Fintype P]
    {bits' : P → ℕ} (N : Network D P bits') (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np) (state : Site.Programs N)
    (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (birthWidth : ∀ j, (state (host j)).birth.work = mult j*(slabs j).stride)
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits')
    (number : Gadget ↪ ℕ) (tags : BottomChoices slabs mult → N.Tables (Entry Param Gadget))
    (model : ∀ z, TagModels N edgeID portID state (tags z) number (carryPred host (birthPredicate slabs mult z)))

local notation3 "size" => placedSize N state
local notation3 "supply" => pathSupply N cell edgeID portID owners slot ports
local notation3 "Bank" => (c : Fin C) → Fin (externalBase N cell c size) → Bool
local notation3 "passes" => CorePassed N cell siteID edgeID portID state host slabs mult birthWidth owners slot ports number tags model

variable (owner : Fin ns → ℕ) (reports : Fin C → List (List ℕ))

/-- The actual zero padding and successful compact cell guards on a
complete distributed choice and its initially unchecked private vectors. -/
def GuardedCores (q : Routed (b:=b) (s:=s) owners) (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool) :
    Prop :=
  Path.Pins N cell slot (rawPath N cell edgeID state owners q raw) ∧ ∀ c : Fin C, ∃ out,
    (FinalCell.directory owner N (fun v => (cell v).val) siteID edgeID portID (fun v => (state v).program)
      c.val (reports c)).guardedObservations (lookup (bank N cell c size (privateWires N cell size c (raw c))
        (privateStaging N cell size c (raw c)) (supply q c))) = some out

local notation3 "guard" => GuardedCores N cell siteID edgeID portID state owners slot ports owner reports
variable (ho : ∀ v, owner (siteID v)=(cell v).val) (birthLocal : ∀ v, (state v).birth.Local)
    (schema : ∀ v, (state v).program.Schema) (relative : ∀ v, (state v).program.RelativeBoxes)

include ho birthLocal schema relative in
/-- All emitted private directories pass exactly on the canonical staged
vectors of the nonzero mathematical source sites. -/
theorem guardedCores_iff (q : Routed (b:=b) (s:=s) owners) (raw : Bank) :
    guard q raw ↔ passes q raw := by
  constructor
  · rintro ⟨pads,guarded⟩
    refine ⟨pads,?_⟩
    intro c v
    obtain ⟨out,ok⟩ := guarded c
    have result := (tagged_native_cell_guard N cell siteID edgeID portID state host slabs mult birthWidth owners supply
      number tags model q c raw owner (reports c) ho birthLocal schema relative out).mp ok
    exact ⟨result.2.1 v,congrFun result.2.2 v⟩
  · rintro ⟨pads,sites⟩
    refine ⟨pads,?_⟩
    intro c
    let z := extractBottom N cell siteID size owners slabs mult (fun _ j => retainedLocation N state host slabs mult birthWidth j) q raw
    let g := privateWires N cell size c (raw c)
    let read := tagReadAt N cell edgeID portID state host slabs mult owners supply number tags model z q c g
    let out := (FinalCell.sites siteID owner c.val).flatMap (fun v => if hv : cell v=c then (read ⟨v,hv⟩).observations else [])
    refine ⟨out,(tagged_native_cell_guard N cell siteID edgeID portID state host slabs mult birthWidth owners supply
      number tags model q c raw owner (reports c) ho birthLocal schema relative out).mpr ?_⟩
    exact ⟨rfl,fun v => (sites c v).1,funext fun v => (sites c v).2⟩

variable (pos : Packet n d blocks → TableEntry n b h K s → Gadget)

/-- Reindex the genuine physical cell-core domain by precisely the passing
tagged paths of (11.2). Every private original and every allocated packet
choice appears once, even when its eventual field coefficient is zero. -/
noncomputable def nativeCoreEquiv :
    {a : Routed (b:=b) (s:=s) owners × Bank // guard a.1 a.2} ≃
      (Σ z : BottomChoices slabs mult, {p : Path N cell n d blocks b h K s // pathTag N cell slot (tags z) ports pos p ≠ 0}) :=
  (Equiv.subtypeEquivRight (p:=fun a : Routed (b:=b) (s:=s) owners × Bank => guard a.1 a.2)
    (q:=fun a : Routed (b:=b) (s:=s) owners × Bank => passes a.1 a.2) fun a => guardedCores_iff N cell siteID edgeID portID state host slabs mult birthWidth
    owners slot ports number tags model owner reports ho birthLocal schema relative a.1 a.2).trans
    (coreEquiv N cell siteID edgeID portID state host slabs mult birthWidth owners slot ports number tags model pos)

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
