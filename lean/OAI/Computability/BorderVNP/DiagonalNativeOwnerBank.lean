import OAI.Computability.BorderVNP.FragmentTaskDirectoryReturn
import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedReportSeed
import OAI.Computability.BorderVNP.RoutingISASignedReaderKeepInputs
import OAI.Computability.BorderVNP.RoutingISASignedPrepReportAllocation
import OAI.Computability.BorderVNP.RoutingISAScheduleClockArgumentVisits

/-! # Physical receiving-team words at the signed task builder

The two-word cell directory precedes the transfer records, the private receiving
banks and the signed fragment arrays. Its owner column survives every report
choice and the subsequent stable fragment bucket.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube FiniteEvaluator DiagonalTallyAllocation DiagonalTallyCellReports
open FragmentRows

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}

/-- Every signed report return leaves the lower region intact apart from the
single descriptor count. The actual tape is recovered from the return, so the
claim applies to arbitrary digits, use flags, and empty owner lists. -/
theorem report_return_before_cells {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {description : ℕ}
    (seed : PreparedReportInput pub m cs q description) (alloc : ReportAllocation pre post banks l cs q)
    (r : Returns prepareCellReports pub mac s m) {x : ℕ} (low : x<banks.bankStart) (ne : x≠l.frame+35) :
    r.val.2.2 x=m x := by
  let E := reportReturnEquiv seed mac s
  let tape := E.symm r
  have eq : E tape=r := E.apply_symm_apply r
  have im := (reportReturnEquiv_spec seed mac s tape).2.2
  rw [prepareWrites_image] at im
  have allocated : ReportAllocation pre post banks l (cellsOfTape cs tape) q := alloc.tape _ _
  rw [←eq]
  exact ReaderKept.afterReports_word allocated im x low ne

variable {a : SignedTaskArena.Layout} {ctl u v k : ℕ}
local notation "head" => readings pub 0
local notation "f" => FragmentRows.Layout.fromFrame head (readings m)

/-- The emitter publishes only its occupied count at control slot 29 below the
fragment arena. The following bucket retains every other word below the cells. -/
theorem fragment_return_before_cells (fit : (f).Fits w (readings m)) (ptr : readings m (head+92)=ctl)
    (words : ∀ i : Fin 37, readings m (ctl+i.val)=a.controls i.val)
    (place : a.SparsePlacement head ctl) (cables : (f).host.count=a.cube.cables)
    (raw : readings m (head+9) ≤ a.cube.maxRows) (cells : readings m (head+11)=a.cube.cells)
    (high : a.endAddress w u v k < 2^w)
    (r : Returns (.seq FragmentRows.program FragmentBucket.program) pub mac s m)
    {x : ℕ} (low : x<a.cube.cellBank) (ne : x≠ctl+29) : readings r.val.2.2 x=readings m x := by
  have order := a.sparse_order place.cells
  have below : ctl+37 ≤ a.fragments.quads := place.beforeBank.trans (order.1.trans order.2.1)
  obtain ⟨e,_,out⟩ := emission_of_return pub mac s m a fit ptr words place.beforeControl below cables raw cells high r.property
  rw [←out]
  have control : (f).control=ctl := ptr
  exact e.original x (control ▸ ne) (.inl (low.trans_le (order.1.trans order.2.1)))

variable {id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ}
    {R team offsets live ports bundles b : ℕ} {axis : Fin (a.cube.n+1)}
    {input orig written : ℕ → ℕ} {l : ReportLayout} {q : ReportCursor}
    {cs : List (ReportCell l)} {description : ℕ}
    (owner : Fin bundles → Fin a.cube.cells) (header : Fin bundles → Packing.BottomReports.BundleHeader)

local notation "H" => a.openInputs team head offsets ctl live ports bundles b owner header
local notation "banks" => a.cube.cellWriter head ctl axis
local notation "weights" => LocalRow.weightLayout a.cube head axis.val
local notation "teams" => LocalRow.teamLayout a.cube R

/-- The exact word input of the real task builder on a complete signed return
is the owner column published by the actual checked team schedule. The owned
handoff supplies the protected public tables, and all following word images
are recovered from the consecutive native returns. -/
theorem owner_bank_on_visits (V : SignedPrep.Visits id pub mac s m)
    (entry : NativeEntry a.cube head ctl axis R input orig written)
    (kept : CubeAllocation.HostRetention a.cube head orig written (readings V.owned.val.2.2))
    (openRoom : a.OpenRoom head offsets ctl live ports bundles (2^b) w)
    (position : OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2))
    (ready : OpenSuffix.Ready H head (readings V.owned.val.2.2) w)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after banks l cs q)
    (place : a.SparsePlacement head ctl)
    (fit : (FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)).Fits w (readings V.reports.val.2.2))
    (ptr : readings V.reports.val.2.2 (head+92)=ctl)
    (words : ∀ i : Fin 37, readings V.reports.val.2.2 (ctl+i.val)=a.controls i.val)
    (cables : (FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)).host.count=a.cube.cables)
    (raw : readings V.reports.val.2.2 (head+9) ≤ a.cube.maxRows)
    (cells : readings V.reports.val.2.2 (head+11)=a.cube.cells) (high : a.endAddress w u v k < 2^w) :
    let parts := (argumentVisitsEquiv pub mac V.reports.val.2.1 V.reports.val.2.2).symm V.arguments
    ∃ scheduled, GroupWeights.ScheduleResult weights teams input scheduled ∧
      ∀ c : Fin a.cube.cells, readings parts.1.val.2.2 ((banks).dest+2*c.val)=
        (banks).written scheduled (banks).cells ((banks).dest+2*c.val) := by
  intro parts
  obtain ⟨scheduled,actual,dir⟩ := entry.image
  refine ⟨scheduled,actual,fun c => ?_⟩
  let x := a.cube.hostDirectory+2*c.val
  obtain ⟨hh,lab,gw,ow,pair,host,_,_⟩ := a.cube.writer_order
  have lt := c.isLt
  have bankEnd := a.open_table_order.2.1
  have floor := kept.primary
  have lower : a.cube.publicBase ≤ x := by dsimp only [x]; omega
  have records : x<a.cube.records := by dsimp only [x]; omega
  have inside : x<a.cube.cellBank := by dsimp only [x]; omega
  have gt : head+112 ≤ x := by omega
  have above : ctl+37 ≤ x := by have := openRoom.controlEnd; omega
  have cut := fragment_return_before_cells fit ptr words place cables raw cells high parts.1 inside (by omega)
  have frame : l.frame=head := seed.framePointer.symm
  have reports := report_return_before_cells seed alloc V.reports (x:=x) inside (by omega)
  have img : readings V.controls.val.2.2=(H).image head (readings V.owned.val.2.2) :=
    ((OpenSuffix.run (H) ready).sound V.controls.property).2
  have clear := a.open_image_low owner header position x inside (by omega)
  have pairEnd : (a.cube.pairWriter head).table+3*(a.cube.pairWriter head).count=a.cube.hostDirectory := by
    change a.cube.pairDirectory+3*(a.cube.alphabet*a.cube.alphabet)=a.cube.pairDirectory+3*a.cube.alphabet^2
    rw [pow_two]
  exact cut.trans ((congrArg Fin.val reports).trans ((congrFun img x).trans (clear.trans
    ((kept.tables x lower records).trans (dir.pairRows.outside x (.inr (by dsimp only [x]; omega)))))))

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
