import OAI.Computability.BorderVNP.DiagonalSameReportVisits
import OAI.Computability.BorderVNP.DiagonalOwnedControlReportSetup
import OAI.Computability.BorderVNP.CubePhysicalReceivedLedgerOrder
import OAI.Computability.BorderVNP.DiagonalCanonicalReportDirectory

/-! # Source reports on the returned control memory and the native cell stream -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.ReportDirectory

open VPVNP.BurstRAM Packing RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep FiniteEvaluator.OpenSuffix
open DiagonalTallyAllocation

variable {l k : ReportLayout} {w description : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s : Bank w} {mem : Memory w} {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout} {q : ReportCursor}

/-- Read the actual grouped headers and delivered one-copy words after the
four native controls, on every proposed assignment in the reindexed source
directory. The report assignment can change every selectable bit. -/
theorem received_source_after_controls (d : BundleDirectory.Layout) (rows : CellControlRows.Layout)
    (owner : Fin d.bundles → Fin d.cells) (source : Fin d.bundles → ReportBundle)
    (sortWidth : ℕ) (counts : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    (ret : Returns controls pub mac s mem) (src : List (ReportCell k)) :
    let H : Inputs := ⟨d,BundleDirectory.groups owner fun j => (source j).header,sortWidth,rows⟩
    let raw := hostImage (pub 0).val (readings mem)
    let cs := directoryCells d rows l owner source (grouped d owner source raw) counts
    H.ReturnImage ret → Bindings pre d rows l → rows.Room w → l.ScannerControls raw →
    l.control+28 ≤ banks.bankStart → (l.control+28 ≤ l.frame ∨ l.frame+96 ≤ l.control) →
    (∀ j,(∃ c∈cs,(owner j).val=c.number) → (source j).delivered l description raw ∧ (source j).SiteRoom l w description) →
    ReportAllocation pre post banks l cs q → SiteIntervals cs description banks.stride → SameReportCells cs src →
    ∀ z : ReportAssignments src, ∀ c ∈ z.val, c.Received w description (readings ret.val.2.2) := by
  intro H raw cs image bind room words before separate delivered alloc intervals same z
  have original := physicalInput_owned d rows l owner source bind w description raw counts room words before separate
    delivered alloc intervals
  exact same.source_received _ (fun c hc => image.2.2.symm ▸ original.received c hc) z

end DiagonalTallyCellReports.ReportDirectory

namespace Cube.Physical.NativeAssignments.ReceivedRows

open DiagonalTallyCellReports

variable {T C : ℕ} {l : ReportLayout} (R : ReceivedRows (fun _ : Fin T => l) C)
    (src : (u : Fin T) → ReportAssignments (R.cells u))

/-- Per-team finite tapes for the proposed source rows, extended by false
beyond the reserved report stream. -/
noncomputable def sourceReportStream (u : Fin T) (p : ℕ) : Bool :=
  if h : p < (reportBits (R.cells u)).length then
    (reportAssignmentEquiv (R.cells u)).symm (src u) ⟨p,h⟩ else false

/-- At the true native owner and compact ordinal, the report chosen on the
entire global stream is the concrete cell of this team's proposal. -/
theorem reportedWithTape_source (u : Fin T) (i : Fin (R.cells u).length) :
    R.reportedWithTape (R.sourceReportStream src) (fun _ => 0) (R.order ⟨u,i⟩) =
      (src u).val.get (Fin.cast (src u).length.symm i) := by
  have same : cellsOfTape (R.cells u) ((reportAssignmentEquiv (R.cells u)).symm (src u))=(src u).val :=
    congrArg Subtype.val ((reportAssignmentEquiv (R.cells u)).apply_symm_apply (src u))
  let get (j : (u : Fin T) × Fin (R.cells u).length) :=
    (tapeCells (R.sourceReportStream src j.1) 0 (R.cells j.1)).get (Fin.cast (tapeCells_length ..).symm j.2)
  refine (congrArg get (R.order.symm_apply_apply ⟨u,i⟩)).trans ?_
  have equalGet : ∀ {xs ys : List (ReportCell l)}, xs=ys →
      ∀ (a : Fin xs.length) (b : Fin ys.length), a.val=b.val → xs.get a=ys.get b := by
    rintro xs _ rfl a b hv
    exact congrArg xs.get (Fin.ext hv)
  exact equalGet same _ _ rfl


end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
