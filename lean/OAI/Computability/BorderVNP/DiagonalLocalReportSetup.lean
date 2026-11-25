import OAI.Computability.BorderVNP.DiagonalOwnedControlReportSetup
import OAI.Computability.BorderVNP.RoutingISASignedPrepOwnedReports

/-! # Physical per-team report data on every chronological choice

The owned directory supplies the same cell descriptors on each control return.
The serializer reads the memory left by the report run for the chosen private
rows, so its fitting conditions can use the corresponding native return.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA

/-- Recover the input of the executable report traversal from the physical
allocation, forgetting only the logical native assignments attached to its cells. -/
theorem ReportSetup.preparedInput {l : ReportLayout} {w : ℕ} {pub : Arg → Word w} {m : Memory w}
    {q : ReportCursor} {description : ℕ} {ss : List (AssignedCell l)} (setup : ReportSetup pub m q description ss) :
    PreparedReportInput pub m (ss.map AssignedCell.report) q description :=
  ⟨setup.framePointer,setup.priorZero,by simpa only [List.length_map] using setup.seeded,setup.frameRoom,setup.controlRoom,
    by simpa only [List.length_map] using setup.headersRoom,setup.rawRoom,setup.arena⟩

end DiagonalTallyCellReports

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalTallyCellReports

/-- Install the actual cell list from the owned directory. Every private row
choice runs on the genuine control return and supplies its own post-report
registers and memory to the sparse serializer. -/
noncomputable def LocalReportData.ofReportSetup {l : ReportLayout} {w : ℕ} {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w} (cs : List (ReportCell l))
    (cursor : ReportCursor) (description : ℕ)
    (ss : (d : Returns controls pub mac s m) → List (AssignedCell l))
    (actual : ∀ d, (ss d).map AssignedCell.report=cs)
    (setup : ∀ d, ReportSetup pub d.val.2.2 cursor description (ss d))
    (arguments : ∀ (d : Returns controls pub mac s m) (r : Returns prepareCellReports pub mac d.val.2.1 d.val.2.2),
      ArgumentInput pub mac r.val.2.1 r.val.2.2) : LocalReportData pub mac s m where
  layout := l
  cells := cs
  cursor := cursor
  description := description
  seed d := actual d ▸ (setup d).preparedInput
  argumentsFit d rows := arguments d (assignedReportReturnEquiv (actual d ▸ (setup d).preparedInput) mac d.val.2.1 rows)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
