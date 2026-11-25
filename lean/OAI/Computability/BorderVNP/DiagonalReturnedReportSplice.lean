import OAI.Computability.BorderVNP.DiagonalPhysicalSparseReportRead
import OAI.Computability.BorderVNP.RoutingISAScheduleClockPublishedFields

/-! # The native builder's ordered sidecar on every sampled report path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open private bundleCursor_tape from OAI.Computability.BorderVNP.RoutingISAScheduleClockReports

private theorem taped_take_cursor {l : ReportLayout} (tape : ℕ → Bool) (cs : List (ReportCell l))
    (p i : ℕ) (q : ReportCursor) :
    ((tapeCells tape p cs).take i).foldl (fun a c => c.after a) q=(cs.take i).foldl (fun a c => c.after a) q := by
  induction cs generalizing p i q with
  | nil => rfl
  | cons c cs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have after : (c.withTape tape p).after q=c.after q := bundleCursor_tape ..
      simp only [tapeCells,List.take_succ_cons,List.foldl_cons,after,ih]

/-- Arbitrary report guesses keep the actual cumulative cursor at each
visited ordinal, even for an empty bundle list. -/
theorem ReportAssignments.take_cursor {l : ReportLayout} {cs : List (ReportCell l)}
    (rows : ReportAssignments cs) (i : ℕ) (q : ReportCursor) :
    (rows.val.take i).foldl (fun a c => c.after a) q=(cs.take i).foldl (fun a c => c.after a) q := by
  let tape := (reportAssignmentEquiv cs).symm rows
  have same : cellsOfTape cs tape=rows.val := congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply rows)
  rw [←same]
  exact taped_take_cursor _ cs 0 i q

end DiagonalTallyCellReports

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM DiagonalTallyCellReports DiagonalTallyAllocation CellSparse Packet

variable {w description : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s : Bank w} {m : Memory w} {a : SignedTaskArena.Layout} {banks : CellBanks.Layout} {rl : ReportLayout}
    {cs : List (ReportCell rl)} {q : ReportCursor} (alloc : ReportAllocation a.before a.after banks rl cs q)
    (seed : PreparedReportInput pub m cs q description) (r : Returns prepareCellReports pub mac s m) (i : Fin cs.length)
    {f : FragmentRows.Layout} {fit : f.Fits w (readings r.val.2.2)} {cells : a.fragments.cells=f.cells}
    (e : FragmentRows.SparseEmission a f r.val.2.2 fit cells) (b : TypedTaskBuilder.Layout) (next : Memory w)
    (image : readings next=b.published (readings e.output))
    (low : b.frame+112≤a.fragments.limit) (control : f.control+37≤a.fragments.limit)
    (high : a.before.limit≤b.calls ∧ a.before.limit≤b.tasks)
local notation3 (prettyPrint := false) "chosen" => (assignedReportReturnEquiv seed mac s).symm r
local notation3 (prettyPrint := false) "row" => (chosen).val[i.val]'(i.isLt.trans_eq (chosen).length.symm)
local notation3 (prettyPrint := false) "cursor" => ((chosen).val.take i.val).foldl (fun a c => c.after a) q

include alloc image low control high in
/-- Decode the live builder memory at the supplement and counter pointers
of this very sampled row. Both cursor and record order refer to the
actual return before fragment emission and compact task production. -/
theorem returned_binding_rows_at_builder :
    readBindingRows (readings next) (rl.supplement+(row).number*rl.supplementStride) (rl.counters+2*(row).number) =
      bindingRows (row).bundles ((row).localStart cursor) := by
  have saved := supplement_at_builder alloc seed r i e b next image low control high
  have number := congrArg ReportCell.number ((chosen).row_eq i)
  change (row).number=cs[i.val].number at number
  rw [number,(chosen).take_cursor i.val q,assigned_bindingRows (chosen) i]
  exact saved.readBindingRows

include alloc image low control high in
/-- The native typed packet appends the exact binding sequence at this
physical ordinal. This identifies every successful merged source, including
before any report guard has been tested. -/
theorem returned_typed_binding_rows {Site : Type} (o : CellPacket.Supplement.Batch.Owned Site)
    {taskBase ctlBase : ℕ} (parsed : MergeFields o taskBase ctlBase i.val next)
    (counters : o.layout.counters=rl.counters+2*(row).number)
    (supplement : o.layout.supplement=rl.supplement+(row).number*rl.supplementStride) :
    o.extra=bindingRows (row).bundles ((row).localStart cursor) := by
  have saved := supplement_at_builder alloc seed r i e b next image low control high
  have number := congrArg ReportCell.number ((chosen).row_eq i)
  change (row).number=cs[i.val].number at number
  rw [number] at counters supplement
  rw [(chosen).take_cursor i.val q,assigned_bindingRows (chosen) i]
  exact saved.mergeRows parsed counters supplement

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
