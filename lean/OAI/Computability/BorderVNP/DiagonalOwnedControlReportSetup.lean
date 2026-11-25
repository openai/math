import OAI.Computability.BorderVNP.DiagonalNativeReportFiber
import OAI.Computability.BorderVNP.RoutingISASignedPrepReportDirectory
import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedControlReturns
import OAI.Computability.BorderVNP.PackedFinalAssignedReport

/-! # Preparing actual signed report guesses after a returning owned-control program

The compact owned rows come from the stable bundle and control producers. The
physical cell assignments are attached to those rows in that order. The signed
report setup follows from the true returned memory image and the address bounds
and delivered original-site words of the native directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM
open scoped Classical

/-- The report instruction and the positive native fiber use the same public
frame, seed, word bounds and genuine source reads at every possible tape. -/
theorem PreparedReportInput.reportSetup {l : ReportLayout} {w : ℕ} {pub : Arg → Word w} {m : Memory w}
    {q : ReportCursor} {description : ℕ} (ss : List (AssignedCell l))
    (setup : PreparedReportInput pub m (ss.map AssignedCell.report) q description) :
    ReportSetup pub m q description ss :=
  ⟨setup.framePointer,setup.first,by simpa only [List.length_map] using setup.seeded,setup.frameRoom,setup.controlRoom,
    by simpa only [List.length_map] using setup.headerRoom,setup.rawRoom,setup.inputs⟩

namespace ReportDirectory

open Crossing Packing Packing.Inherited Packing.CellAddresses CellSparse
open FiniteEvaluator.OpenSuffix DiagonalTallyAllocation
open RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep

variable {D ns ne np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable (N : Network D P bits) (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (siteOwner : Fin ns → ℕ) (state : N.Site → Site)
variable (g : ∀ c, Fin (guessedSize N cell c) → Bool)
variable (a : ∀ c, Fin (siteSize N cell c (fun v => (state v).size)) → Bool)
variable (x : ∀ c, Fin (suppliedSize N cell c) → Bool)
variable (bottom : ℕ → List BottomReports.Bundle) (observed : ℕ → List (Bool × Option ℕ))

/-- Attach the actual private wire choices, supplied words and original box
inventory to each compact row at its own global cell. -/
noncomputable def assigned {l : ReportLayout} (cs : List (ReportCell l)) :=
  cs.map fun r => FinalCell.assignedReport N cell r.number siteID edgeID portID siteOwner state r
    (g r.number) (a r.number) (x r.number) (bottom r.number) (observed r.number)

/-- Erasing the private assignment leaves the native producer's original rows. -/
theorem assigned_report {l : ReportLayout} (cs : List (ReportCell l)) :
    (assigned N cell siteID edgeID portID siteOwner state g a x bottom observed cs).map AssignedCell.report = cs := by
  simp [assigned,FinalCell.assignedReport,List.map_map,Function.comp_def]

variable {w : ℕ} {p : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
variable {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout} {l : ReportLayout} {q : ReportCursor}

/-- Every actual four-stage control return with its proved image enters signed
report preparation on the compact directory's real header, source and count
tables. No prior report choices are used in the source-read certification. -/
theorem setup_after_controls (d : BundleDirectory.Layout) (rows : CellControlRows.Layout)
    (owner : Fin d.bundles → Fin d.cells) (source : Fin d.bundles → ReportBundle)
    (sortWidth description : ℕ) (counts : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    (ret : Returns controls p mac s m) :
    let H : Inputs := ⟨d,BundleDirectory.groups owner fun j => (source j).header,sortWidth,rows⟩
    let raw := hostImage (p 0).val (readings m)
    let middle := grouped d owner source raw
    let cs := directoryCells d rows l owner source middle counts
    let ss := assigned N cell siteID edgeID portID siteOwner state g a x bottom observed cs
    H.ReturnImage ret → Bindings pre d rows l → (p 0).val=l.frame → l.seed q (raw (l.frame+90)) raw →
    rows.Room w → l.ScannerControls raw → l.control+28 ≤ banks.bankStart →
    (l.control+28 ≤ l.frame ∨ l.frame+96 ≤ l.control) →
    (∀ j, (∃ c∈cs, (owner j).val=c.number) → (source j).delivered l description raw ∧ (source j).SiteRoom l w description) →
    l.fieldWidth ≤ w → l.parameters+l.gadgets < 2^w → l.fieldWidth+l.bodyCap < 2^w → post.fresh < 2^w →
    ReportAllocation pre post banks l cs q → SiteIntervals cs description banks.stride →
    (∀ c∈cs, c.privateWires+c.supplied+c.tailWidth<2^w) → ReportSetup p ret.val.2.2 q description ss := by
  intro H raw middle cs ss actual bind fp seed room ctrl controlBefore apart delivered width coord rawRoom space alloc slots endFit
  have image : readings ret.val.2.2=rows.published middle := actual.2.2
  have real := preparedInput_owned d rows owner source raw counts bind fp seed room ctrl controlBefore apart
    delivered width coord rawRoom space alloc slots endFit image
  have original := assigned_report N cell siteID edgeID portID siteOwner state g a x bottom observed cs
  exact PreparedReportInput.reportSetup ss (original.symm ▸ real)

end ReportDirectory
end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
