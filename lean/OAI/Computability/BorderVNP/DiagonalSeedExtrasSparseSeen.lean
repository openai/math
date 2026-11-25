import OAI.Computability.BorderVNP.DiagonalSignedNativePacketSeeds
import OAI.Computability.BorderVNP.DiagonalNativeReportBindings
import OAI.Computability.BorderVNP.DiagonalReceivedReportExtent
import OAI.Computability.BorderVNP.DiagonalNativeOwnedCellInputs

/-! # The sparse argument with the actual selected report's supplemental rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open Crossing Packing Packing.Inherited Packing.BottomReports Packing.CellAddresses
open RoutingISA RoutingISA.CompactMachine CellMacro.Generator CellSparse DiagonalTallyCellReports DiagonalTallyAllocation

variable {T C D ns ne np : ℕ} {P J Origin : Type} [Fintype P] {bits : P → ℕ} {layouts : Fin T → ReportLayout}
    (R : ReceivedRows layouts C) (N : Network D P bits) (cell : N.Site → Fin C)
    (sites : N.Site ↪ Fin ns) (edges : N.Edge ↪ Fin ne) (ports : P ↪ Fin np)
    (owners : Fin ns → ℕ) (state : Site.Programs N) (bundle : J → Bundle) (body : J → List Factor)
    (bank : J → ℕ → Bool) (origins : Fin C → List J)
    (u : Fin T) (i : Fin (R.cells u).length)
local notation3 (prettyPrint := false) "num" => R.order ⟨u,i⟩
local notation3 (prettyPrint := false) "cellKey" => fun v => (cell v).val
local notation3 (prettyPrint := false) "program" => fun v => (state v).program
local notation3 (prettyPrint := false) "base" => FinalCell.countBase N cellKey program (num).val
local notation3 (prettyPrint := false) "counts" => (layouts u).gadgets*(layouts u).countWidth

/-- At the sparse task's true global cell number, append the actual source's
binding rows to the genuine sorted original directory. Every private-use ties
to the appropriate lane after the supplied inputs and count digits. -/
theorem sparse_seen {a : SignedTaskArena.Layout} {banks : CellBanks.Layout} {q : ReportCursor}
    (alloc : ReportAllocation a.before a.after banks (layouts u) (R.cells u) q)
    (template : ((R.cells u).get i).bundles=(origins num).map fun j =>
      physicalBundle (bundle j).header (body j) (bundle j).factors (bank j))
    (stride : ∀ j∈origins num, (bundle j).header.stride=bottomStride (bundle j).header.orig (bundle j).header.cap)
    (extent : ((R.cells u).get i).privateWires+((R.cells u).get i).supplied=base)
    (placed : CellPacket.Placed Origin) (field : SparseExterior.Field)
    (shape : placed.directory=FinalCell.directory owners N cellKey sites edges ports program (num).val
      (countFields base (layouts u).gadgets (layouts u).countWidth) ∧
      placed.privateWires=FinalCell.privateBits N cellKey program (num).val) :
    SparseExterior.logicalCell placed (seedExtras (R.cells u) q (num).val) field =
      FinalCell.withWiring (FinalCell.cellInput N cellKey sites edges ports owners program (num).val
        (layouts u).gadgets (layouts u).countWidth field.values) (supplements (base+counts) ((origins num).map bundle)) := by
  let row := (R.cells u).get i
  let cursor := ((R.cells u).take i.val).foldl (fun z x => x.after z) q
  have extra : seedExtras (R.cells u) q (num).val=supplements (base+counts) ((origins num).map bundle) := by
    have address : seedExtras (R.cells u) q (num).val=seedExtras (R.cells u) q row.number :=
      congrArg (seedExtras (R.cells u) q) (R.number u i).symm
    have actual := alloc.seedExtras_owned i
    change seedExtras (R.cells u) q row.number=bindingRows row.bundles (row.localStart cursor) at actual
    have calculate := bindingRows_physical (origins num) bundle body bank (row.localStart cursor) stride
    have start : (row.localStart cursor).privateUse=base+counts := congrArg (·+counts) extent
    exact (address.trans actual).trans ((congrArg (fun bs => bindingRows bs (row.localStart cursor)) template).trans
      (calculate.trans (congrArg (fun z => supplements z ((origins num).map bundle)) start)))
  change CellInput.mk (appendRows placed.directory _) placed.privateWires _=_
  rw [shape.1,shape.2,extra]
  rfl

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
