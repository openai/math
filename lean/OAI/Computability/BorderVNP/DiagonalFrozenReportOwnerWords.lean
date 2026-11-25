import OAI.Computability.BorderVNP.DiagonalReportEmissionOwners
import OAI.Computability.BorderVNP.DiagonalFrozenPaddingControls

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Owner words of a returned report on the actual frozen writer -/

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalTallyAllocation DiagonalTallyCellReports FiniteEvaluator
open TeamContraction.ProcessorSlots FragmentRows TeamContraction BorderVNP.Cube TypedTaskBuilder

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {m : Memory w}
    (V : ReportsThrough pub mac reg m) (a : SignedTaskArena.Layout)
    {R team base offsets ctl live ports bundles bits description : ℕ}
    (owner : Fin bundles → Fin a.cube.cells) (header : Fin bundles → Packing.BottomReports.BundleHeader)
    {l : ReportLayout} {q : ReportCursor} {cs : List (ReportCell l)} {banks : CellBanks.Layout}
local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "H" => a.openInputs team base offsets ctl live ports bundles bits owner header
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)
local notation3 (prettyPrint := false) "cols" => a.controlRows team head offsets ctl live ports

/-- On this team's actual proposed report, the control pointer still addresses the frozen control vector
and every emitted owner word is the one written by the original native directory program. -/
theorem ReportsThrough.frozenNativeOwners {axis : Fin (a.cube.n+1)} {nativeControl : ℕ}
    {input original written : ℕ → ℕ} {supply : Fin a.cube.cells → ℕ}
    (native : NativeEntry a.cube base nativeControl axis R input original written)
    (who : ℕ → ℕ) (selected : ∀ c : Fin a.cube.cells,
      (a.cube.receivingOwner base axis R input c.val).val=who c.val)
    (frozen : FrozenControlEntry a H base head ctl offsets w supply written (readings m))
    (room : a.OpenRoom base offsets ctl live ports bundles (2^bits) w)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after banks l cs q) (bankStart : banks.bankStart=a.cube.cellBank)
    {fit : (f).Fits w (readings V.reports.val.2.2)} {cells : a.fragments.cells=(f).cells}
    (e : SparseEmission a f V.reports.val.2.2 fit cells) :
    readings V.reports.val.2.2 (head+92)=ctl ∧
      ∀ c : Fin a.cube.cells, (cols).owner (readings e.output) c.val=who c.val := by
  have same := frozen.frame
  subst base
  obtain ⟨_,_,image⟩ := native.image
  obtain ⟨hh,lab,gw,ow,pair,host,_,_⟩ := a.cube.writer_order
  have low := a.open_table_order
  have primary := room.primary
  have endCtl := room.controlEnd
  have afterFrame := frozen.frameEnd
  have opened := ((OpenSuffix.run _ frozen.ready).sound V.controls.property).2
  have keep (x : ℕ) (inBanks : x<a.cube.cellBank) (n35 : x≠head+35) (n90 : x≠head+90) :
      readings V.reports.val.2.2 x=readings m x := by
    have chart := seed.framePointer
    have saved := ScheduleClock.report_return_before_cells seed alloc V.reports
      (x:=x) (bankStart ▸ inBanks) (chart ▸ n35)
    exact (congrArg Fin.val saved).trans ((congrFun opened x).trans
      (a.open_image_low owner header frozen.placement x inBanks n90))
  have ptr := (keep (head+92) (by omega) (by omega) (by omega)).trans frozen.controlWord
  refine ⟨ptr,fun c => ?_⟩
  let x := a.cube.hostDirectory+2*c.val
  have hc := c.isLt
  have inside : x<a.cube.cellBank := by dsimp only [x]; omega
  have order := a.sparse_order room.cells
  have control : (f).control=ctl := ptr
  have emitted := e.original x (by rw [control]; dsimp only [x]; omega)
    (.inl (inside.trans_le (order.1.trans order.2.1)))
  have keepOwner := keep x inside (by dsimp only [x]; omega) (by dsimp only [x]; omega)
  have originalOwner := (image.hostRows c.val hc).1
  rw [Nat.mul_comm c.val 2] at originalOwner
  have table := frozen.retained.tables x (by dsimp only [x]; omega) (by dsimp only [x]; omega)
  exact emitted.trans (keepOwner.trans (table.trans (originalOwner.trans (selected c))))

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
