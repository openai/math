import OAI.Computability.BorderVNP.DiagonalSameReportVisits
import OAI.Computability.BorderVNP.RoutingISASignedPrepOwnedReports

/-! # Fitted inputs on the observed control and report returns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalTallyCellReports ScheduleClock

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s t : Bank w} {m v : Memory w} {l : ReportLayout} {ds : List (ReportCell l)}

/-- The fitted report scanner and argument writer on the same reached states,
together with the actual values of all the report choices. -/
structure ReportArgumentCut (actual : Returns prepareCellReports pub mac t v)
    (src : ReportAssignments ds) (q : ReportCursor) (description : ℕ) where
  /-- The scanner starts at the actual control memory. -/
  seed : PreparedReportInput pub v ds q description
  /-- Its chronological private tape agrees with the original assignment. -/
  chosen : (reportAssignmentEquiv ds).symm src = (reportReturnEquiv seed mac t).symm actual
  /-- The sparse argument program reads the observed report bank and memory. -/
  argument : ArgumentInput pub mac actual.val.2.1 actual.val.2.2

/-- Use equality of the native return values to put both fitted programs
on the observed execution. The source and physical report directories
may differ in all their sampled fields. -/
noncomputable def LocalReportData.observedCut (data : LocalReportData pub mac s m)
    (ctl : Returns controls pub mac s m) (same : SameReportCells data.cells ds)
    (src : ReportAssignments ds) (actual : Returns prepareCellReports pub mac t v)
    (start : (t,v)=ctl.val.2)
    (returned : actual.val=(assignedReportReturnEquiv (data.seed ctl) mac ctl.val.2.1 (same.equiv.symm src)).val) :
    ReportArgumentCut actual src data.cursor data.description := by
  have eqReg : t=ctl.val.2.1 := congrArg Prod.fst start
  have eqMem : v=ctl.val.2.2 := congrArg Prod.snd start
  subst t v
  have run := Subtype.ext returned
  let fit := data.argumentsFit ctl (same.equiv.symm src)
  exact ⟨same.source_seed (data.seed ctl), (same.returned_source_tape (data.seed ctl) mac ctl.val.2.1 src run).symm,
    (congrArg (fun z => ArgumentInput pub mac z.2.1 z.2.2) returned).mpr fit⟩

/-- The typed-task memory seen on the true sparse suffix is the builder's
published image. In particular the writer's fitted sparse source can be
evaluated on this very memory. -/
theorem ArgumentInput.visited_publication (fit : ArgumentInput pub mac s m) (args : Returns arguments pub mac s m) :
    let parts := (argumentVisitsEquiv pub mac s m).symm args
    readings parts.2.1.val.2.2=fit.tasks.published (readings parts.1.val.2.2) := by
  intro parts
  obtain ⟨_,_,_,run,_,image⟩ := TypedTaskBuilder.program_run pub mac parts.1.val.2.1 parts.1.val.2.2
    fit.tasks fit.frame (fit.fields parts.1) (fit.room parts.1)
  exact (congrArg readings (parts.2.1.property.unique_of_deterministic (by decide) run).2.2).trans image

/-- The sparse launcher selected by the checked local builder on the
attained argument history. -/
noncomputable def ArgumentInput.visitedSource (fit : ArgumentInput pub mac s m) (args : Returns arguments pub mac s m) :
    let parts := (argumentVisitsEquiv pub mac s m).symm args
    SparseCallInput pub parts.2.1.val.2.2 :=
  fit.sparse _ _ (fit.visited_publication args)

/-- The fragment emitter's fitted layout is exactly the one loaded from
the observed post-report memory. -/
theorem ReportArgumentCut.fragment_fit {actual : Returns prepareCellReports pub mac t v} {src : ReportAssignments ds}
    {q : ReportCursor} {description : ℕ} (cut : ReportArgumentCut actual src q description) :
    (FragmentRows.Layout.fromFrame (pub 0).val (readings actual.val.2.2)).Fits w (readings actual.val.2.2) :=
  cut.argument.fragments.loaded ▸ cut.argument.fragments.fit

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
