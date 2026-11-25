import OAI.Computability.BorderVNP.DiagonalReturnedSparseCell
import OAI.Computability.BorderVNP.DiagonalExternalFragmentSourceWords

/-! # The true input prefix of a receiving cell survives every report store -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalTallyAllocation

variable {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}

private theorem ReportAllocation.unique_number (alloc : ReportAllocation pre post banks l cs q)
    {c v : ReportCell l} (hc : c∈cs) (hv : v∈cs) (number : c.number=v.number) : c=v := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hc
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hv
  obtain ⟨rows,names⟩ := alloc.owned
  have agree : rows i=rows j := Fin.ext ((names i).symm.trans (number.trans (names j)))
  exact congrArg cs.get (rows.injective agree)

private theorem ReportAllocation.before_tail (alloc : ReportAllocation pre post banks l cs q)
    {c v : ReportCell l} (hc : c∈cs) (hv : v∈cs) (j : Fin c.supplied) (s : ReportWrite)
    (writer : s.within (v.external+v.supplied) (v.external+v.supplied+v.tailWidth)) :
    c.external+j.val<s.address ∨ s.address+s.data.length≤c.external+j.val := by
  have jSmall := j.isLt
  obtain ⟨lo,hi⟩ := writer
  rcases lt_trichotomy c.number v.number with earlier|same|later
  · obtain ⟨start,size⟩ := alloc.receiving c hc
    obtain ⟨next,_⟩ := alloc.receiving v hv
    have endLe := Nat.mul_le_mul_right banks.stride earlier
    rw [Nat.succ_mul] at endLe
    simp only [CellBanks.Layout.bank] at start next
    omega
  · obtain rfl := alloc.unique_number hc hv same
    omega
  · obtain ⟨start,size⟩ := alloc.receiving v hv
    obtain ⟨next,_⟩ := alloc.receiving c hc
    have endLe := Nat.mul_le_mul_right banks.stride later
    rw [Nat.succ_mul] at endLe
    simp only [CellBanks.Layout.bank] at start next
    omega

/-- Every counted or weighted use entry is appended after the supplied
bits of its own bank. No other owned cell can overwrite this input range. -/
theorem ReportAllocation.suppliedPrefix (alloc : ReportAllocation pre post banks l cs q)
    (c : ReportCell l) (owned : c∈cs) (j : Fin c.supplied) :
    ∀ s∈prepareWrites cs q, c.external+j.val<s.address ∨ s.address+s.data.length≤c.external+j.val := by
  have ready := (alloc.banksOrdered c owned).1
  rw [alloc.widths] at ready
  change c.external+c.supplied+c.tailWidth ≤ pre.start at ready
  have index := j.isLt
  have bank := (alloc.receiving c owned).1
  have frame := alloc.frameBefore
  have mid : pre.start≤pre.limit := by rw [pre.footprint]; omega
  have packed : post.start≤post.packed ∧ post.packed≤post.refs ∧ post.refs≤post.descriptors := by
    simp only [AfterTasks.descriptors,AfterTasks.refs,AfterTasks.packed,AfterTasks.ids,AfterTasks.lookupRefs,
      AfterTasks.lookupRows]
    omega
  intro z hz
  rw [prepareWrites,List.mem_append] at hz
  rcases hz with body|last
  · rcases cellWrites_range cs q z body with stream|⟨v,hv,cell⟩
    · simp only [cursorRange,ReportWrite.within,alloc.initial] at stream
      left
      have := alloc.preBefore
      omega
    · simp only [cellRange] at cell
      rcases cell with supp|counters|width|tail
      · left
        have low := supp.1
        rw [alloc.supplement] at low
        simp only [BeforeTasks.supplement,BeforeTasks.tailWidths] at low
        omega
      · left
        have low := counters.1
        rw [alloc.counters] at low
        simp only [BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.tailWidths] at low
        omega
      · left
        have low := width.1
        rw [alloc.widths] at low
        change pre.start+v.number≤z.address at low
        omega
      · exact alloc.before_tail owned hv j z tail
  · obtain rfl := List.mem_singleton.mp last
    right
    change l.frame+35+1≤c.external+j.val
    simp only [CellBanks.Layout.bank] at bank
    omega

/-- On any returning report path, all originally supplied values in an
owned cell are exactly the words in memory before sampling its report. -/
theorem returned_report_supply {w description : ℕ} {pub : Arg → Word w} {m : Memory w}
    {mac : TeamOpcode.Macros w 8} {s : Bank w} (alloc : ReportAllocation pre post banks l cs q)
    (seed : PreparedReportInput pub m cs q description) (r : Returns prepareCellReports pub mac s m)
    (i : Fin cs.length) (j : Fin cs[i.val].supplied) :
    readings r.val.2.2 (cs[i.val].external+j.val)=readings m (cs[i.val].external+j.val) := by
  let e := assignedReportReturnEquiv seed mac s
  let rows := e.symm r
  let tape := (reportAssignmentEquiv cs).symm rows
  have same : cellsOfTape cs tape=rows.val := congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply rows)
  have newAlloc : ReportAllocation pre post banks l rows.val q := same ▸ alloc.tape _ _
  let i' : Fin rows.val.length := Fin.cast rows.length.symm i
  let row := rows.val[i'.val]
  have addr := congrArg ReportCell.external (rows.row_eq i)
  change row.external=cs[i.val].external at addr
  have size := congrArg ReportCell.supplied (rows.row_eq i)
  change row.supplied=cs[i.val].supplied at size
  have image := (assignedReportReturnEquiv_spec seed mac s rows).2
  rw [show assignedReportReturnEquiv seed mac s rows=r from e.apply_symm_apply r,prepareWrites_image] at image
  rw [image,←addr]
  exact writes_outside _ _ _ (newAlloc.suppliedPrefix row (List.getElem_mem _) (j.cast size.symm))

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
