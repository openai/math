import OAI.Computability.BorderVNP.DiagonalSparseReportOrdinals
import OAI.Computability.BorderVNP.DiagonalReturnedHostSupply

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Ownership after a fragment emission on a report-only suffix -/

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalTallyAllocation DiagonalTallyCellReports FiniteEvaluator
open TeamContraction.ProcessorSlots FragmentRows TeamContraction BorderVNP.Cube TypedTaskBuilder

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    (a : SignedTaskArena.Layout) {team offsets ctl live ports bundles b description : ℕ}
    (V : ReportsThrough pub mac s m) (owner : Fin bundles → Fin a.cube.cells)
    (header : Fin bundles → Packing.BottomReports.BundleHeader)
    {l : ReportLayout} {q : ReportCursor} {cs : List (ReportCell l)}
local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "H" => a.openInputs team head offsets ctl live ports bundles b owner header
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)
local notation3 (prettyPrint := false) "cols" => a.controlRows team head offsets ctl live ports

/-- The original schedule's owner number remains in the real cell-control row
through report sampling and the stable bucket. No typed task output is used. -/
theorem ReportsThrough.owners_at_emission (axis : Fin (a.cube.n+1))
    (room : a.OpenRoom head offsets ctl live ports bundles (2^b) w)
    (position : OpenSuffix.Placement H a.cube a.before head (readings m))
    (ready : OpenSuffix.Ready H head (readings m) w)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter head ctl axis) l cs q)
    {fit : (f).Fits w (readings V.reports.val.2.2)} {cells : a.fragments.cells=(f).cells}
    (e : SparseEmission a f V.reports.val.2.2 fit cells) (ptr : readings V.reports.val.2.2 (head+92)=ctl)
    (who : ℕ → ℕ) (source : ∀ c : Fin a.cube.cells,readings m (a.cube.hostDirectory+2*c.val)=who c.val) :
    ∀ c : Fin a.cube.cells, (cols).owner (readings e.output) c.val=who c.val := by
  intro c
  let x := a.cube.hostDirectory+2*c.val
  obtain ⟨hh,lab,gw,ow,pair,host,_,_⟩ := a.cube.writer_order
  have lt := c.isLt
  have bankEnd := a.open_table_order.2.1
  have floor := room.primary
  have above := room.controlEnd
  have inside : x<a.cube.cellBank := by dsimp only [x]; omega
  have order := a.sparse_order room.cells
  have cover : (f).control=ctl := ptr
  have cut := e.original x (by rw [cover]; dsimp only [x]; omega) (.inl (inside.trans_le (order.1.trans order.2.1)))
  have frame : l.frame=head := seed.framePointer.symm
  have reports := ScheduleClock.report_return_before_cells seed alloc V.reports (x:=x) inside (by dsimp only [x]; omega)
  have image : readings V.controls.val.2.2=(H).image head (readings m) :=
    ((OpenSuffix.run (H) ready).sound V.controls.property).2
  have clear := a.open_image_low owner header position x inside (by dsimp only [x]; omega)
  exact cut.trans ((congrArg Fin.val reports).trans ((congrFun image x).trans (clear.trans (source c))))

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
