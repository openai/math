import OAI.Computability.BorderVNP.DiagonalPositiveCoreReceived
import OAI.Computability.BorderVNP.RoutingISASignedPrepOwnedReports

/-! # The native received report rows are independent of the original private choices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

/-- Transport assignments between two received directories that agree after
erasing the proposed digits. The actual list of report rows is kept literally. -/
def sameReportAssignments {l : ReportLayout} {cs ds : List (ReportCell l)}
    (same : eraseReportBits cs=eraseReportBits ds) : ReportAssignments cs ≃ ReportAssignments ds where
  toFun x := ⟨x.val,x.property.trans same⟩
  invFun x := ⟨x.val,x.property.trans same.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

end DiagonalTallyCellReports

namespace Cube.Physical.NativeAssignments.ReceivedRows

open VPVNP.BurstRAM Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs
open RoutingISA RoutingISA.Evaluator DiagonalTallyCellReports DiagonalResidueRAM

variable {D C ns ne np n d blocks b h K s T w : ℕ} {P Team : Type} [Fintype P]
    {bits : P → ℕ} {layout : Fin T → ReportLayout} (R : ReceivedRows layout C)
    (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)
    (owner : Fin ns → ℕ) (bottom : Fin C → List Bundle) (q : Routed (b:=b) (s:=s) owners)
    (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)
    (physical : ∀ u,List (ReportCell (layout u))) (same : ∀ u,eraseReportBits (physical u)=eraseReportBits (R.cells u))

local notation3 "ss" => R.assigned N cell siteID edgeID portID state owners slot ports owner bottom q raw

/-- The reports indexed by the physical preparation and the reports indexed
by the original core have exactly the same rows, even on a failed original
core and on every malformed report. -/
noncomputable def physicalReportEquiv :
    ((u : Fin T) → ReportAssignments (physical u)) ≃ NativeReports ss :=
  Equiv.piCongrRight fun u => sameReportAssignments ((same u).trans (congrArg eraseReportBits
    (R.assigned_report N cell siteID edgeID portID state owners slot ports owner bottom q raw u)).symm)

local notation3 "E" => R.physicalReportEquiv N cell siteID edgeID portID state owners slot ports owner bottom q raw physical same

/-- Both directions keep every proposed physical byte and its immutable cell
header at the same team and native ordinal. -/
theorem physicalReportEquiv_rows (r : (u : Fin T) → ReportAssignments (physical u)) (u : Fin T) :
    ((E r) u).val=(r u).val := rfl

theorem physicalReportEquiv_symm_rows (r : NativeReports ss) (u : Fin T) :
    (((E).symm r) u).val=(r u).val := rfl

/-- Read the chronological physical report choices and the resulting cell
images on an arbitrary original-core-indexed assignment through the actual
native report-return bijection. -/
theorem physicalReportEquiv_return (u : Fin T) {pub : Arg → Word w} {mem : Memory w} {cursor : ReportCursor} {description : ℕ}
    (seed : PreparedReportInput pub mem (physical u) cursor description)
    (mac : TeamOpcode.Macros w 8) (reg : Bank w) (r : NativeReports ss) :
    let z := assignedReportReturnEquiv seed mac reg ((E).symm r u)
    TraceOK z.val.1 (reportBits (r u).val) z.val.1.length ∧
      readings z.val.2.2=Function.update (cellImages (r u).val cursor (readings mem))
        ((layout u).frame+35) (cellOperands (r u).val cursor).length :=
  assignedReportReturnEquiv_spec seed mac reg ((E).symm r u)

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
