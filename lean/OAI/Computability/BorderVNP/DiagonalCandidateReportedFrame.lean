import OAI.Computability.BorderVNP.DiagonalFrozenPaddingControls
import OAI.Computability.BorderVNP.DiagonalSignedReportFragmentHeader

/-! # Fragment inputs preserved by the genuine owned and report returns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator Packing BottomReports
open RoutingISA.Evaluator.SignedPrep FiniteEvaluator DiagonalTallyCellReports DiagonalTallyAllocation

variable {w team base ctl offsets live ports bundles b : ℕ} (t : SignedTaskArena.Layout)
    (owner : Fin bundles → Fin t.cube.cells) (headers : Fin bundles → BundleHeader)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {owned : Memory w}
    {supply : Fin t.cube.cells → ℕ} {input : ℕ → ℕ}
local notation "H" => t.openInputs team base offsets ctl live ports bundles b owner headers
local notation "rows" => t.controlRows team base offsets ctl live ports

/-- The report scanner changes its guess stream and private output buffers.
The original frame and the geometry control table remain readable on every
return, using the physical seed and allocation that precede the report. -/
theorem FrozenControlEntry.reported_fields
    (stage : FrozenControlEntry t H base (pub 0).val ctl offsets w supply input (readings owned))
    (fields : t.OpenFields team base offsets ctl live ports bundles input)
    (width : input (base+30)=w) (limit : input (base+14)=t.before.limit)
    (tasks : input (base+89)=(rows).tasks)
    (room : t.OpenRoom base offsets ctl live ports bundles (2^b) w)
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {desc : ℕ} {banks : CellBanks.Layout}
    (advance : Returns SignedPrep.controls pub mac s owned)
    (run : Returns prepareCellReports pub mac advance.val.2.1 advance.val.2.2)
    (seed : PreparedReportInput pub advance.val.2.2 cs q desc)
    (alloc : ReportAllocation t.before t.after banks l cs q) (bank : banks.bankStart=t.cube.cellBank) :
    (rows).Fields (readings run.val.2.2) ∧ readings run.val.2.2 (base+30)=w ∧
      readings run.val.2.2 (base+14)=t.before.limit ∧ readings run.val.2.2 (base+89)=(rows).tasks ∧
      readings run.val.2.2 (base+92)=ctl ∧ ∀ i : Fin 37, readings run.val.2.2 (ctl+i.val)=t.controls i.val := by
  have frame : l.frame=base := seed.framePointer.symm.trans stage.frame
  have openImage := ((OpenSuffix.run H stage.ready).sound advance.property).2
  have low (z : ℕ) (before : z<t.cube.header.header) (n35 : z≠base+35) (n90 : z≠base+90) : readings run.val.2.2 z=readings owned z := by
    have below := before.trans_le t.open_table_order.1
    have preserved := ScheduleClock.report_return_before_cells seed alloc run (x:=z) (bank ▸ below) (frame ▸ n35)
    have wrote := congrFun openImage z
    change _=(H).image (pub 0).val (readings owned) z at wrote
    rw [stage.frame] at wrote
    exact (congrArg Fin.val preserved).trans (wrote.trans (t.open_image_low owner headers stage.placement z below n90))
  have read (i : ℕ) (small : i<112) (a : i≠13) (b' : i≠35) (c : i≠46) (d : i≠90) :
      readings run.val.2.2 (base+i)=input (base+i) := by
    have space : base+i<t.cube.header.header := by have := stage.retained.primary; omega
    exact (low _ space (by omega) (by omega)).trans (stage.retained.lower _ space (by omega) (by omega))
  have after := fields.transfer t (m':=readings run.val.2.2) fun i hi => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    exact read i (by omega) (by omega) (by omega) (by omega) (by omega)
  have controls (j : Fin 37) : readings run.val.2.2 (ctl+j.val)=t.controls j.val := by
    have first := stage.frameEnd
    exact (low _ (by have := room.controlEnd; omega) (by omega) (by omega)).trans (stage.controls j)
  exact ⟨(after.inputs t controls).2,(read 30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans width,
    (read 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans limit,
    (read 89 (by decide) (by decide) (by decide) (by decide) (by decide)).trans tasks,after.controlWord,controls⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
