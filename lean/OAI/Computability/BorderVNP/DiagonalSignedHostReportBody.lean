import OAI.Computability.BorderVNP.DiagonalSignedOpaqueReportRetention
import OAI.Computability.BorderVNP.DiagonalReportSupplyPreserved
import OAI.Computability.BorderVNP.FiniteEvaluatorOpenedHostWords

/-! # Report-bound original verifier bytes after the selected host scatter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM RoutingISA.Evaluator FiniteEvaluator DiagonalTallyCellReports CellSparse.Packet.Source
open private ReportAllocation.unique_number from OAI.Computability.BorderVNP.DiagonalReportSupplyPreserved

/-- A genuine report source on the emitted host image gives the original
verifier bytes at the same address in every returning signed report. Bounds
come from the complete native report's actual site intervals. -/
theorem Layout.host_to_report_body (a : Layout) {w description ctl : ℕ} {pub : Arg → Word w} {entry : Memory w}
    {reg : Bank w} {mac : TeamOpcode.Macros w 8} (H : OpenSuffix.Inputs)
    (ready : OpenSuffix.Ready H (pub 0).val (readings entry) w)
    (placed : OpenSuffix.Placement H a.cube a.before (pub 0).val (readings entry))
    (first : (pub 0).val+112≤a.cube.header.header) (opened : Returns OpenSuffix.code pub mac reg entry)
    {axis : Fin (a.cube.n+1)} {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter (pub 0).val ctl axis) l cs q)
    (seed : PreparedReportInput pub opened.val.2.2 cs q description)
    (run : Returns prepareCellReports pub mac opened.val.2.1 opened.val.2.2)
    (intervals : SiteIntervals cs description a.cube.cellStride)
    (i : Fin cs.length) (b : ReportBundle) (existsIn : b∈cs[i.val].bundles)
    (full : b.delivered l description (OpenSuffix.hostImage (pub 0).val (readings entry)))
    (room : b.SiteRoom l w description) :
    Delivered (description:=description) (readings run.val.2.2) b.header.siteSlot l.fieldWidth b.factors := by
  have hr := List.getElem_mem (l:=cs) i.isLt
  let c : Fin a.cube.cells := ⟨cs[i.val].number,alloc.bankNumber _ hr⟩
  let bank := a.cube.cellBank+c.val*a.cube.cellStride
  let start := b.header.siteSlot-bank
  obtain ⟨lower,upper⟩ := intervals _ hr b existsIn
  have base : cs[i.val].external=bank := (alloc.receiving _ hr).1
  rw [base] at lower upper
  have address : bank+start=b.header.siteSlot := by dsimp only [start]; omega
  have inBank : start+description≤a.cube.cellStride := by omega
  have original := (siteWithTally_read _ _ _ _ _ _ room.body room.descriptionRoom full).1
  have received : Delivered (description:=description) (readings opened.val.2.2) (bank+start) l.fieldWidth b.factors := by
    intro bit used
    let pos : Fin a.cube.cellStride := ⟨start+bit.val,by have := bit.isLt; omega⟩
    have kept := a.opened_host_word H ready placed first opened c pos
    change readings opened.val.2.2 (bank+(start+bit.val))=OpenSuffix.hostImage (pub 0).val (readings entry) (bank+(start+bit.val)) at kept
    rw [←Nat.add_assoc] at kept
    rw [kept,address]
    exact original bit used
  have tails (row : ReportCell l) (member : row∈cs) (same : row.number=c.val) : row.supplied+row.tailWidth≤ start := by
    have eqn : row=cs[i.val] := ReportAllocation.unique_number alloc member hr same
    rw [eqn]
    omega
  have kept := returned_opaque alloc seed run c start l.fieldWidth b.factors inBank tails received
  change Delivered (description:=description) (readings run.val.2.2) (bank+start) l.fieldWidth b.factors at kept
  rwa [address] at kept

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
