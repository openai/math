import OAI.Computability.BorderVNP.DiagonalPositiveOwnedReportSource
import OAI.Computability.BorderVNP.DiagonalPositiveReportMap

/-! # Issue the actual sparse dispatch from its returned logical inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open VPVNP.BurstRAM Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs
open RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine RoutingISA.SparseExterior DiagonalTallyCellReports
open scoped Classical

variable {D C ns ne np n d blocks b h K s T : ℕ} {P Team : Type} [Fintype P]
    {bits : P → ℕ} {layout : Fin T → ReportLayout} (R : ReceivedRows layout C)
    (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)
    (owner : Fin ns → ℕ) (bottom : Fin C → List Bundle) (q : Routed (b:=b) (s:=s) owners)
    (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)
    (reports : NativeReports (R.assigned N cell siteID edgeID portID state owners slot ports owner bottom q raw))

local notation3 "key" => (fun v => (cell v).val)
local notation3 "progs" => (fun v => (state v).program)
local notation3 "atRow" => R.assignedAt N cell siteID edgeID portID state owners slot ports owner bottom q raw
local notation3 "allRows" => R.assigned N cell siteID edgeID portID state owners slot ports owner bottom q raw
local notation3 (prettyPrint := false) "num" => (fun (u : Fin T) (i : Fin (R.cells u).length) => R.order ⟨u,i⟩)
local notation3 (prettyPrint := false) "supply" => pathSupply N cell edgeID portID owners slot ports q
local notation3 (prettyPrint := false) "reportAt" => (fun (u : Fin T) (i : Fin (R.cells u).length) =>
  (reports u).val.get (Fin.cast (((assignedRows_length (reports u)).trans (List.length_ofFn (f := atRow u))).symm) i))

variable {dim box lanes selectors symbols w order : ℕ} {id : TableEntry dim box lanes selectors symbols → ℕ}
    (S : Fin T → PositiveTeam id SparseExterior.driver order w) (p : ∀ u,(S u).Prefix)

/-- Package the complete native input before the core is guessed. The private
sidecar directory is the one emitted from the retained originals. -/
noncomputable def sourceCall (u : Fin T) (i : Fin (R.cells u).length) : CellInput :=
  let c := num u i
  let start := FinalCell.countBase N key progs c.val+(layout u).gadgets*(layout u).countWidth
  FinalCell.withWiring (FinalCell.cellInput N key siteID edgeID portID owner progs c.val (layout u).gadgets
    (layout u).countWidth (List.ofFn (supply c)++(reportAt u i).bits)) (supplements start (bottom c))

/-- A genuine sparse publication with the physical field restored and the actual
selected immutable bindings produces the exact logical cell of this report. -/
theorem sourceCall_of_seen {Origin : Type} (u : Fin T) (i : Fin (R.cells u).length) (placed : CellPacket.Placed Origin)
    (extra : List CellSparse.Record) (field : SparseExterior.Field)
    (restored : field.values=List.ofFn (supply (num u i))++(reportAt u i).bits) :
    let c := num u i
    SparseExterior.logicalCell placed extra field=
      FinalCell.withWiring (FinalCell.cellInput N key siteID edgeID portID owner progs c.val (layout u).gadgets
        (layout u).countWidth field.values) (supplements
          (FinalCell.countBase N key progs c.val+(layout u).gadgets*(layout u).countWidth) (bottom c)) →
    SparseExterior.logicalCell placed extra field=
      sourceCall R N cell siteID edgeID portID state owners slot ports owner bottom q raw reports u i := by
  intro c actual
  rw [restored] at actual
  exact actual

/-- The native schedule has issued every field on the returned report. The
single supported prefix and its observed dispatcher are used before any
successful bank or selected report is assumed. -/
noncomputable def NativeCallInputs.ofSourceCall
    (published : ∀ u (i : Fin (R.cells u).length), ((S u).generated (p u)).cell (num u i).val=
      sourceCall R N cell siteID edgeID portID state owners slot ports owner bottom q raw reports u i) :
    NativeCallInputs R N cell siteID edgeID portID state owners slot ports owner bottom q raw reports S p := by
  refine ⟨fun u => ((S u).generated (p u)).cell,fun _ => rfl,?_⟩
  intro u i
  rw [published u i]
  let c := num u i
  let a := atRow u i
  let ext := List.ofFn (supply c)++(reportAt u i).bits
  have initial : a.initial=(FinalCell.cellInput N key siteID edgeID portID owner progs c.val (layout u).gadgets
      (layout u).countWidth ext).directory := by
    rw [R.assignedAt_directory]
    simp only [ReceivedRows.countReports,c,Equiv.symm_apply_apply,FinalCell.cellInput]
  have cursor : a.privateWires+a.boundary.length=FinalCell.countBase N key progs c.val := by
    change FinalCell.privateBits N key progs c.val+(List.ofFn _).length=_
    rw [List.length_ofFn]
    rfl
  have extEq := R.assignedAt_boundary N cell siteID edgeID portID state owners slot ports owner bottom q raw u i
  change CellInput.mk (appendRows _ (supplements _ (bottom c))) _ ext=
    CellInput.mk (appendRows a.initial (supplements (a.privateWires+a.boundary.length+
      (layout u).gadgets*(layout u).countWidth) a.bundles)) _ (a.boundary++(reportAt u i).bits)
  rw [initial,cursor,extEq]
  rfl

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
