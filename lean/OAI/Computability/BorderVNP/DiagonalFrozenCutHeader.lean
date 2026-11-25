import OAI.Computability.BorderVNP.DiagonalSourcePhysicalReportCursor
import OAI.Computability.BorderVNP.DiagonalFrozenPaddingControls

/-! # The source report and fragment header of an attained frozen opening -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM FiniteEvaluator DiagonalTallyCellReports DiagonalTallyAllocation TeamContraction
open TeamContraction.JointHeader SignedTaskArena ScheduleClock

variable {w team base ctl offsets live ports bundles b raw reserve axes groups cap width : ℕ}
    (sa : SignedTaskArena.Layout) (owner : Fin bundles → Fin sa.cube.cells)
    (header : Fin bundles → Packing.BottomReports.BundleHeader)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bank : Bank w} {entry : Memory w}
    {layout : ReportLayout} {cells : List (ReportCell layout)} {cursor : ReportCursor} {description : ℕ}
local notation3 (prettyPrint := false) "H" => sa.openInputs team base offsets ctl live ports bundles b owner header

/-- Read the allocator's report cursor and all six fragment operands directly
on the true control and report memories. Only three original size words come
from outside the attained opening's receipt. -/
theorem ReportArgumentCut.header_on_frozen_control (opened : Returns controls pub mac bank entry)
    (report : Returns prepareCellReports pub mac opened.val.2.1 opened.val.2.2)
    {source : ReportAssignments cells} (cut : ReportArgumentCut report source cursor description)
    {claimed : PositiveFields reserve axes groups cap sa.cube.teams sa.dim width}
    (copied : HeaderSeed sa claimed pub raw team entry)
    {supplied : Fin sa.cube.cells → ℕ} {initial : ℕ → ℕ}
    (frozen : FrozenControlEntry sa H base (pub 0).val ctl offsets w supplied initial (readings entry))
    (room : ctl+37 ≤ sa.cube.header.header) (control : layout.control=ctl)
    {bl : CellBanks.Layout} (alloc : ReportAllocation sa.before sa.after bl layout cells sa.after.reportCursor)
    (bankAt : bl.bankStart=sa.cube.cellBank)
    (cables : readings entry (base+7)=sa.cube.cables) (rows : readings entry (base+9) ≤ sa.cube.maxRows)
    (cellCount : readings entry (base+11)=sa.cube.cells) :
    ∃ actual : ReportArgumentCut report source sa.after.reportCursor description, actual.argument=cut.argument ∧
      let out := readings report.val.2.2
      (FragmentRows.Layout.fromFrame (pub 0).val out).Fits w out ∧ out ((pub 0).val+92)=ctl ∧
        (∀ j : Fin 37, out (ctl+j.val)=sa.controls j.val) ∧ (FragmentRows.Layout.fromFrame (pub 0).val out).host.count=sa.cube.cables ∧
        out ((pub 0).val+9) ≤ sa.cube.maxRows ∧ out ((pub 0).val+11)=sa.cube.cells := by
  have baseEq := frozen.frame
  subst base
  obtain rfl := physical_report_cursor sa owner header opened cut.seed copied frozen.ready frozen.placement
    frozen.frameEnd room control frozen.controls
  have limit := sa.open_table_order.1
  have fixedFrame := frozen.frameEnd
  have beforeBank : ctl+37 ≤ sa.cube.cellBank := room.trans limit
  have chartFrame := cut.seed.framePointer
  have image := ((OpenSuffix.run _ frozen.ready).sound opened.property).2
  have keep (j : ℕ) (low : j<sa.cube.cellBank) (n35 : j≠(pub 0).val+35) (n90 : j≠(pub 0).val+90) :
      readings report.val.2.2 j=readings entry j := by
    have kept := report_return_before_cells cut.seed alloc report (x:=j) (bankAt ▸ low) (chartFrame ▸ n35)
    exact (congrArg Fin.val kept).trans ((congrFun image j).trans (sa.open_image_low owner header frozen.placement j low n90))
  refine ⟨cut,rfl,cut.fragment_fit,(keep _ (by omega) (by omega) (by omega)).trans frozen.controlWord,fun i => ?_,
    (keep _ (by omega) (by omega) (by omega)).trans cables,(keep _ (by omega) (by omega) (by omega)).trans_le rows,
    (keep _ (by omega) (by omega) (by omega)).trans cellCount⟩
  have := i.isLt
  exact (keep _ (by omega) (by omega) (by omega)).trans (frozen.controls i)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
