import OAI.Computability.BorderVNP.DiagonalOwnedVisitReconstruction
import OAI.Computability.BorderVNP.RoutingISASignedPrepOwnedReports

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # The actual control, returned report and typed-argument suffix of a reconstructed source path -/

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube DiagonalTallyCellReports

variable {w dim b h K s : ℕ} (id : TableEntry dim b h K s → ℕ)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {start : Bank w} {initial : Memory w}

/-- The inverse of the fitted report traversal preserves the actual full
return at all three final cuts, including its chosen report stream. -/
theorem visits_rebuilt_tail (sched : Returns (schedule dim K h) pub mac start initial)
    (empty : sched.val.1.flatMap TeamRAM.Event.choices=[])
    (r : Returns route pub mac sched.val.2.1 sched.val.2.2)
    (c : Returns (CubeConstants.install id) pub mac r.val.2.1 r.val.2.2)
    (o : Returns (TeamRows.ownedGroups dim b h K s) pub mac c.val.2.1 c.val.2.2)
    (ctl : Returns controls pub mac o.val.2.1 o.val.2.2)
    (d : LocalReportData pub mac o.val.2.1 o.val.2.2) (rows : ReportAssignments d.cells) :
    let report := assignedReportReturnEquiv (d.seed ctl) mac ctl.val.2.1 rows
    let args := (arguments_returns (d.argumentsFit ctl rows)).some
    let tail := (fittedReportTailEquiv ctl (d.seed ctl) (d.argumentsFit ctl)).symm rows
    let full := (fixedScheduleEquiv id sched empty) ⟨r,(inputCut id pub mac c).symm ⟨o,tail⟩⟩
    let v := (visitsEquiv id pub mac start initial).symm full
    (v.controls.val,v.reports.val,v.arguments.val)=(ctl.val,report.val,args.val) := by
  intro report args tail full v
  have eqn := visits_rebuilt id sched empty r c o tail
  exact congrArg (fun x : Visits id pub mac start initial => (x.controls.val,x.reports.val,x.arguments.val)) eqn

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
