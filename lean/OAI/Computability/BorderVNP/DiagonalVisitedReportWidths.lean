import OAI.Computability.BorderVNP.DiagonalPreparedBundleRows
import OAI.Computability.BorderVNP.DiagonalPhysicalSparseReportRead

/-! # Recovering each returned sparse tail width on the local report owner scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator TypedTaskBuilder DiagonalTallyAllocation

variable {w description : ℕ} {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {pub : Arg → Word w} {m : Memory w} {mac : TeamOpcode.Macros w 8} {s : Bank w}
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}

/-- The real signed report return published the unfilled row's tail width at
its original global number for every choice of its count and use bits. -/
theorem returned_report_width (alloc : ReportAllocation pre post banks l cs q)
    (seed : PreparedReportInput pub m cs q description) (ret : Returns prepareCellReports pub mac s m) (i : Fin cs.length) :
    readings ret.val.2.2 (l.tailWidths+cs[i].number)=cs[i].tailWidth := by
  let chosen := (assignedReportReturnEquiv seed mac s).symm ret
  let j : Fin chosen.val.length := ⟨i.val,i.isLt.trans_eq chosen.length.symm⟩
  have actual := returned_report_binding alloc seed ret j
  have same := chosen.row_eq i
  have ordinal := congrArg ReportCell.number same
  have number : chosen.val[j].number=cs[i].number := ordinal
  have width : chosen.val[j].tailWidth=cs[i].tailWidth :=
    (congrArg ReportCell.tailWidth same).trans (ReportCell.withTape_tailWidth ..)
  exact (congrArg (fun k => readings ret.val.2.2 (l.tailWidths+k)) number.symm).trans (actual.width.trans width)

/-- The word indexed by an owned global number on the actual report return
holds the width of the selected source row. -/
theorem returned_owned_width (layout : CellControlRows.Layout) (raw : ℕ → ℕ) (atCell : ℕ → ReportCell l)
    (numbers : ∀ c, (atCell c).number=c) (csEq : cs=visitedReportRows layout raw atCell)
    (alloc : ReportAllocation pre post banks l cs q) (seed : PreparedReportInput pub m cs q description)
    (ret : Returns prepareCellReports pub mac s m) (c : ℕ) (realCell : c<layout.cells)
    (owned : layout.owner raw c=layout.team) :
    readings ret.val.2.2 (l.tailWidths+c)=(atCell c).tailWidth := by
  subst cs
  obtain ⟨i,_,selected⟩ := visitedReportRows_owned layout raw atCell c realCell owned
  have width := returned_report_width alloc seed ret i
  change readings ret.val.2.2 (l.tailWidths+((visitedReportRows layout raw atCell).get i).number)=
    ((visitedReportRows layout raw atCell).get i).tailWidth at width
  rwa [selected,numbers] at width

/-- The actual native report return determines its chronological count and use
stream, padded with false only beyond the last requested digit. -/
noncomputable def PreparedReportInput.returnedTape (seed : PreparedReportInput pub m cs q description)
    (ret : Returns prepareCellReports pub mac s m) (k : ℕ) : Bool :=
  let chosen := (assignedReportReturnEquiv seed mac s).symm ret
  let tape := (reportAssignmentEquiv cs).symm chosen
  if h : k < (reportBits cs).length then tape ⟨k,h⟩ else false

/-- Offset of the first chosen bit of the indicated global cell on this
one native team, following every preceding local row in chronological order. -/
def returnedTapePosition (layout : CellControlRows.Layout) (raw : ℕ → ℕ) (source : List (ReportCell l)) (c : ℕ) : ℕ :=
  ((source.take (layout.before raw c)).map ReportCell.tailWidth).sum

/-- Stable compact enumeration of the proposed global source cells reconstructs
the exact returned assignment, including all digits of rejected private reports. -/
theorem PreparedReportInput.returnedVisitedRows (layout : CellControlRows.Layout) (raw : ℕ → ℕ)
    (atCell : ℕ → ReportCell l) (order : cs=visitedReportRows layout raw atCell)
    (seed : PreparedReportInput pub m cs q description) (ret : Returns prepareCellReports pub mac s m) :
    visitedReportRows layout raw (fun c => (atCell c).withTape (seed.returnedTape ret)
      (returnedTapePosition layout raw cs c)) = ((assignedReportReturnEquiv seed mac s).symm ret).val := by
  let chosen := (assignedReportReturnEquiv seed mac s).symm ret
  have length : cs.length = layout.before raw layout.cells := by
    rw [order,visitedReportRows,List.length_ofFn]
  apply List.ext_getElem
  · simpa only [visitedReportRows,List.length_ofFn] using length.symm.trans chosen.length.symm
  · intro i hi hi'
    have inRange : i<cs.length := hi'.trans_eq chosen.length
    let j : Fin cs.length := ⟨i,inRange⟩
    have native := chosen.row_eq j
    change chosen.val[i]=cs[i].withTape (seed.returnedTape ret) ((cs.take i).map ReportCell.tailWidth).sum at native
    have range : i<layout.before raw layout.cells := j.isLt.trans_eq length
    have cell : cs[i]=atCell (globalCell layout.toLayout raw i) := by
      calc
        cs[i] = (visitedReportRows layout raw atCell)[i]'(order ▸ inRange) := getElem_congr_coll order
        _ = _ := by simp only [visitedReportRows,List.getElem_ofFn]
    have pos := (global_spec layout.toLayout raw range).2.2
    simp only [visitedReportRows,List.getElem_ofFn]
    rw [native,cell]
    exact congrArg ((atCell _).withTape _) (congrArg (fun k => ((cs.take k).map ReportCell.tailWidth).sum) pos)

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
