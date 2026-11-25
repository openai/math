import OAI.Computability.BorderVNP.DiagonalPositiveOwnedReportInputs
import OAI.Computability.BorderVNP.DiagonalNativeReportBindings
import OAI.Computability.BorderVNP.DiagonalNativeArgumentCells
import OAI.Computability.BorderVNP.DiagonalNativeTerminalCell

/-! # The sparse typed source of a received original bank and its actual report -/

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
variable {Orig : Fin T → Type} (placed : ∀ u, ℕ → CellPacket.Placed (Orig u))
    (extra : Fin T → ℕ → List CellSparse.Record) (field : Fin T → ℕ → SparseExterior.Field)
    (cursor : ∀ u, Fin (R.cells u).length → ReportCursor)
local notation3 (prettyPrint := false) "binding" => (fun (u : Fin T) (i : Fin (R.cells u).length) =>
  bindingRows (reportAt u i).bundles ((reportAt u i).localStart (cursor u i)))

/-- Construct the row image from the global sparse typed arguments of the
actual positive preparations. The terminal geometry proof reads the sorted
private packet. The sparse restoration reads its routed supply and its own
guessed tail. The physical supplement writer is evaluated here on every
arbitrary report using the original sites in their delivered order. -/
noncomputable def NativeCallInputs.ofOwnedTerminal
    (published : ∀ u (i : Fin (R.cells u).length), let c := (num u i).val
      ((S u).generated (p u)).cell c = logicalCell (placed u c) (extra u c) (field u c))
    (spliced : ∀ u i, extra u (num u i).val=binding u i)
    (decoded : ∀ u i, (field u (num u i).val).values=List.ofFn (supply (num u i))++(reportAt u i).bits)
    (terminal : ∀ u i, let c := num u i
      (field u c.val).values=List.ofFn (supply c)++(reportAt u i).bits →
        logicalCell (placed u c.val) (binding u i) (field u c.val)=
          FinalCell.withWiring (FinalCell.cellInput N key siteID edgeID portID owner progs c.val (layout u).gadgets
            (layout u).countWidth (List.ofFn (supply c)++(reportAt u i).bits)) (binding u i))
    {Source : Type*} (origins : Fin C → List Source) (bundle : Source → Bundle)
    (body : Source → List CellSparse.Factor) (bank : Source → ℕ → Bool)
    (inventory : ∀ c, bottom c=(origins c).map bundle)
    (stored : ∀ u (i : Fin (R.cells u).length), ((R.cells u).get i).bundles =
      (origins (num u i)).map (fun j => physicalBundle (bundle j).header (body j) (bundle j).factors (bank j)))
    (stride : ∀ c j, j∈origins c → (bundle j).header.stride=bottomStride (bundle j).header.orig (bundle j).header.cap)
    (sizes : ∀ u (i : Fin (R.cells u).length), ((R.cells u).get i).privateWires+((R.cells u).get i).supplied =
      FinalCell.countBase N key progs (num u i).val) :
    NativeCallInputs R N cell siteID edgeID portID state owners slot ports owner bottom q raw reports S p := by
  refine ⟨fun u => ((S u).generated (p u)).cell,fun _ => rfl,?_⟩
  intro u i
  rw [published u i]
  let c := num u i
  let s := atRow u i
  have original := R.assigned_report N cell siteID edgeID portID state owners slot ports owner bottom q raw u
  let r : ReportAssignments (R.cells u) := ⟨(reports u).val, by
    rw [← original]
    exact (reports u).property⟩
  have binding_eq := assigned_physical_supplements r i (cursor u i) (origins c) bundle body bank (stored u i) (stride c)
  change binding u i = supplements (((R.cells u).get i).privateWires+((R.cells u).get i).supplied+
    (layout u).gadgets*(layout u).countWidth) ((origins c).map bundle) at binding_eq
  rw [sizes u i,← inventory] at binding_eq
  have external := R.assignedAt_boundary N cell siteID edgeID portID state owners slot ports owner bottom q raw u i
  have init : s.initial=(FinalCell.cellInput N key siteID edgeID portID owner progs c.val (layout u).gadgets
      (layout u).countWidth (List.ofFn (supply c)++(reportAt u i).bits)).directory := by
    rw [R.assignedAt_directory]
    simp only [ReceivedRows.countReports,c,Equiv.symm_apply_apply,FinalCell.cellInput]
  have start : s.privateWires+s.boundary.length=FinalCell.countBase N key progs c.val := by
    change FinalCell.privateBits N key progs c.val+(List.ofFn _).length=_
    rw [List.length_ofFn]
    rfl
  have bundles : s.bundles=bottom c := rfl
  have finish := terminal u i (decoded u i)
  rw [spliced u i,finish]
  change CellInput.mk (appendRows _ (binding u i)) _ (List.ofFn (supply c)++(reportAt u i).bits) =
    CellInput.mk (appendRows s.initial (supplements (s.privateWires+s.boundary.length+
      (layout u).gadgets*(layout u).countWidth) s.bundles)) _ (s.boundary++(reportAt u i).bits)
  rw [init,start,binding_eq,bundles,external]
  rfl

/-- Specialize the occupied-row constructor when the serializer presents the
whole array of original argument functions. -/
noncomputable abbrev NativeCallInputs.ofTerminal
    (published : ∀ u, ((S u).generated (p u)).cell =
      fun c => logicalCell (placed u c) (extra u c) (field u c)) :=
  NativeCallInputs.ofOwnedTerminal R N cell siteID edgeID portID state owners slot ports owner bottom q raw reports
    S p placed extra field cursor (fun u i => congrFun (published u) (num u i).val)

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
