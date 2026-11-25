import OAI.Computability.BorderVNP.DiagonalSignedReportFragmentHeader
import OAI.Computability.BorderVNP.DiagonalSignedReportEntry

/-! # The physical starting cursor of a recovered signed report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalTallyCellReports DiagonalTallyAllocation SignedTaskArena
open FiniteEvaluator TeamContraction.JointHeader

variable {w team offsets ctl live ports bundles b reserve axes groups cap width raw : ℕ}
    (sa : SignedTaskArena.Layout) (owner : Fin bundles → Fin sa.cube.cells)
    (header : Fin bundles → Packing.BottomReports.BundleHeader)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bank : Bank w} {entry : Memory w}
    {l : ReportLayout} {cs : List (ReportCell l)} {cur : ReportCursor} {description : ℕ}
local notation3 (prettyPrint := false) "frame" => (pub 0).val
local notation3 (prettyPrint := false) "H" => sa.openInputs team (pub 0).val offsets ctl live ports bundles b owner header

/-- A local builder that prepares a source report on the attained memory
necessarily uses the physical descriptor, packed-operand and reference bases.
The report layout may be related to the selected one by equality of its
frame and control addresses alone. -/
theorem physical_report_cursor (opened : Returns controls pub mac bank entry)
    (seed : PreparedReportInput pub opened.val.2.2 cs cur description)
    {p : PositiveFields reserve axes groups cap sa.cube.teams sa.dim width}
    (copied : HeaderSeed sa p pub raw team entry)
    (ready : OpenSuffix.Ready H frame (readings entry) w)
    (placement : OpenSuffix.Placement H sa.cube sa.before frame (readings entry))
    (start : frame+112 ≤ ctl) (finish : ctl+37 ≤ sa.cube.header.header)
    (controlAt : l.control=ctl) (words : ∀ i : Fin 37, readings entry (ctl+i.val)=sa.controls i.val) :
    cur=sa.after.reportCursor := by
  have image := ((OpenSuffix.run H ready).sound opened.property).2
  have high := sa.open_table_order.1
  have held (x : ℕ) (bound : x<sa.cube.cellBank) (unchanged : x≠frame+90) :
      readings opened.val.2.2 x=readings entry x :=
    (congrFun image x).trans (sa.open_image_low owner header placement x bound unchanged)
  obtain ⟨_,_,_,_,ds,_,_,_,_,_,pk,refs,_⟩ := seed.seeded
  have atFrame : l.frame=frame := seed.framePointer.symm
  rw [atFrame] at ds
  rw [controlAt] at pk refs
  have descriptor : cur.descriptors=sa.after.descriptors :=
    ds.symm.trans ((held _ (by omega) (by omega)).trans copied.seed.words.1)
  have packed : cur.packed=sa.after.packed :=
    pk.symm.trans ((held _ (by omega) (by omega)).trans (words 25))
  have references : cur.refs=sa.after.refs :=
    refs.symm.trans ((held _ (by omega) (by omega)).trans (words 26))
  have zero := seed.first
  cases cur
  simp_all only [AfterTasks.reportCursor]

/-- On the recovered execution the report tape is the exact chosen source
tape, with the startup cursor used by the final operand ledger. -/
theorem ReportArgumentCut.physical_tape (opened : Returns controls pub mac bank entry)
    (report : Returns prepareCellReports pub mac opened.val.2.1 opened.val.2.2)
    {src : ReportAssignments cs} (cut : ReportArgumentCut report src cur description)
    {p : PositiveFields reserve axes groups cap sa.cube.teams sa.dim width}
    (copied : HeaderSeed sa p pub raw team entry)
    (ready : OpenSuffix.Ready H frame (readings entry) w)
    (placement : OpenSuffix.Placement H sa.cube sa.before frame (readings entry))
    (start : frame+112 ≤ ctl) (finish : ctl+37 ≤ sa.cube.header.header)
    (controlAt : l.control=ctl) (words : ∀ i : Fin 37, readings entry (ctl+i.val)=sa.controls i.val) :
    ∃ seed : PreparedReportInput pub opened.val.2.2 cs sa.after.reportCursor description,
      (reportAssignmentEquiv cs).symm src=(reportReturnEquiv seed mac opened.val.2.1).symm report := by
  obtain rfl := physical_report_cursor sa owner header opened cut.seed copied ready placement start finish controlAt words
  exact ⟨cut.seed,cut.chosen⟩

/-- Both programs on the attained cut use the cursor of the selected post arena. -/
theorem ReportArgumentCut.atPhysicalCursor (opened : Returns controls pub mac bank entry)
    (report : Returns prepareCellReports pub mac opened.val.2.1 opened.val.2.2)
    {src : ReportAssignments cs} (cut : ReportArgumentCut report src cur description)
    {p : PositiveFields reserve axes groups cap sa.cube.teams sa.dim width}
    (copied : HeaderSeed sa p pub raw team entry)
    (ready : OpenSuffix.Ready H frame (readings entry) w)
    (placement : OpenSuffix.Placement H sa.cube sa.before frame (readings entry))
    (start : frame+112 ≤ ctl) (finish : ctl+37 ≤ sa.cube.header.header)
    (controlAt : l.control=ctl) (words : ∀ i : Fin 37, readings entry (ctl+i.val)=sa.controls i.val) :
    Nonempty (ReportArgumentCut report src sa.after.reportCursor description) := by
  obtain ⟨seed,chosen⟩ := cut.physical_tape sa owner header opened report copied ready placement start finish controlAt words
  exact ⟨⟨seed,chosen,cut.argument⟩⟩

/-- Recover both the selected allocator's cursor and its fragment header
from the boot words of the original physical writer. The physical scanner
identifies even the control pointer of the source layout on this execution. -/
theorem ReportArgumentCut.allocator_and_fragment (opened : Returns controls pub mac bank entry)
    (report : Returns prepareCellReports pub mac opened.val.2.1 opened.val.2.2)
    {src : ReportAssignments cs} (cut : ReportArgumentCut report src cur description)
    {p : PositiveFields reserve axes groups cap sa.cube.teams sa.dim width} (copied : HeaderSeed sa p pub raw team entry)
    {initial written : ℕ → ℕ} (keep : CubeAllocation.HostRetention sa.cube frame initial written (readings entry))
    (ready : OpenSuffix.Ready H frame (readings entry) w) (placement : OpenSuffix.Placement H sa.cube sa.before frame (readings entry))
    (start : frame+112 ≤ ctl) (finish : ctl+37 ≤ sa.cube.header.header)
    (fields : sa.OpenFields team frame offsets ctl live ports bundles initial) (words : ∀ i : Fin 37, initial (ctl+i.val)=sa.controls i.val)
    (entries : initial (frame+9) ≤ sa.cube.maxRows) (cells : initial (frame+11)=sa.cube.cells)
    {bl : CellBanks.Layout} (alloc : ReportAllocation sa.before sa.after bl l cs sa.after.reportCursor)
    (bankStart : bl.bankStart=sa.cube.cellBank) :
    ∃ realCut : ReportArgumentCut report src sa.after.reportCursor description, realCut.argument=cut.argument ∧
      let data := readings report.val.2.2
      (FragmentRows.Layout.fromFrame frame data).Fits w data ∧ data (frame+92)=ctl ∧
        (∀ j : Fin 37, data (ctl+j.val)=sa.controls j.val) ∧ (FragmentRows.Layout.fromFrame frame data).host.count=sa.cube.cables ∧
          data (frame+9) ≤ sa.cube.maxRows ∧ data (frame+11)=sa.cube.cells := by
  have bound := keep.primary
  have access := ((OpenSuffix.run H ready).sound opened.property).2
  have low := sa.open_table_order.1
  have before : frame+92 < sa.cube.header.header := by omega
  have control : l.control=ctl := by
    have atFrame := cut.seed.framePointer
    have rd := cut.seed.seeded.1
    rw [←atFrame] at rd
    exact rd.symm.trans ((congrFun access _).trans ((sa.open_image_low owner header placement _ (before.trans_le low)
      (by omega)).trans ((keep.lower _ before (by omega) (by omega)).trans fields.controlWord)))
  have loaded (i : Fin 37) : readings entry (ctl+i.val)=sa.controls i.val := by
    have := i.isLt
    exact (keep.geometry start (ctl+i.val) (by omega) (by omega)).trans (words i)
  obtain rfl := physical_report_cursor sa owner header opened cut.seed copied ready placement start finish control loaded
  exact ⟨cut,rfl,cut.header_from_profile sa owner header opened report keep ready placement alloc bankStart start finish fields words entries cells⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
