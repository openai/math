import OAI.Computability.BorderVNP.DiagonalPhysicalSparseReportRead

/-! # Sparse cell launch from the actual returned weighted-use report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalTallyAllocation
open scoped Classical

private theorem six_at {l : ReportLayout} (m : ℕ → ℕ) (cs : List (ReportCell l)) (base : ℕ)
    (input : CellPacket.WordsAt m base (cs.flatMap ReportCell.headerWords)) (i : Fin cs.length) :
    CellPacket.WordsAt m (base+6*i.val) cs[i.val].headerWords := by
  induction cs generalizing base with
  | nil => exact i.elim0
  | cons c tail ih =>
    change CellPacket.WordsAt m base (c.headerWords++tail.flatMap ReportCell.headerWords) at input
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using input.left
    · have rest := ih (base+c.headerWords.length) input.right j
      have len : c.headerWords.length=6 := rfl
      simpa only [List.getElem_cons_succ,Fin.val_succ,len,Nat.mul_succ,Nat.add_assoc,
        Nat.add_left_comm,Nat.add_comm] using rest

/-- A genuine report return preserves the initial six-word header of every
owned cell, in its original team-local ordinal. -/
theorem returned_report_header {w description : ℕ} {l : ReportLayout} {cs : List (ReportCell l)}
    {q : ReportCursor} {pub : Arg → Word w} {m : Memory w} {mac : TeamOpcode.Macros w 8} {s : Bank w}
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    (alloc : ReportAllocation pre post banks l cs q) (seed : PreparedReportInput pub m cs q description)
    (input : CellPacket.WordsAt (readings m) l.headers (cs.flatMap ReportCell.headerWords))
    (r : Returns prepareCellReports pub mac s m) (i : Fin cs.length) :
    let rows := (assignedReportReturnEquiv seed mac s).symm r
    CellPacket.WordsAt (readings r.val.2.2) (pre.six+6*i.val)
      (rows.val[i.val]'(i.isLt.trans_eq rows.length.symm)).headerWords := by
  intro rows
  let e := assignedReportReturnEquiv seed mac s
  let tape := (reportAssignmentEquiv cs).symm rows
  have same : cellsOfTape cs tape=rows.val := congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply rows)
  have alloc' : ReportAllocation pre post banks l (cellsOfTape cs tape) q := alloc.tape _ _
  rw [same] at alloc'
  have image := (assignedReportReturnEquiv_spec seed mac s rows).2
  rw [show assignedReportReturnEquiv seed mac s rows=r from e.apply_symm_apply r,prepareWrites_image] at image
  have head := six_at (readings m) cs l.headers input i
  rw [alloc.headers] at head
  have saved := congrArg ReportCell.headerWords (rows.row_eq i)
  rw [ReportCell.withTape_headerWords] at saved
  rw [saved]
  intro j
  have hj : j.val<6 := j.isLt
  have hi := i.isLt.trans_le alloc.owned_le
  have band : pre.merged≤pre.six ∧ pre.six+6*pre.bound.cells≤pre.limit := by
    simp only [BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.six,BeforeTasks.four]
    omega
  have last : post.start≤post.packed := by
    simp only [AfterTasks.packed,AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]
    omega
  have frame : l.frame+35<pre.six := by
    have := alloc.frameBefore
    have := alloc.bankBefore
    simp only [BeforeTasks.six,BeforeTasks.four,BeforeTasks.merged,BeforeTasks.counters,
      BeforeTasks.supplement,BeforeTasks.tailWidths]
    omega
  rw [image]
  refine (writes_outside _ _ _ ?_).trans (head j)
  intro z hz
  rw [prepareWrites,List.mem_append] at hz
  rcases hz with yes|yes
  · rcases alloc'.outsideMiddle z yes with lo|upper
    · exact Or.inr (lo.trans (by omega))
    · exact Or.inl (by have := alloc.preBefore; omega)
  · obtain rfl := List.mem_singleton.mp yes
    exact Or.inr (by change l.frame+35+1 ≤ pre.six+6*i.val+j.val; omega)

/-- Construct the original compact sparse row on the scanner's own returned
memory, at its actual global ordinal. Its suffix is chosen by the native
execution. The initial record header supplies both six-word fields. -/
noncomputable def sparseCellOfReportReturn {w description : ℕ} {l : ReportLayout} {cs : List (ReportCell l)}
    {q : ReportCursor} {pub : Arg → Word w} {m : Memory w} {mac : TeamOpcode.Macros w 8} {s : Bank w}
    (a : SignedTaskArena.Layout) (banks : CellBanks.Layout) (f : FragmentRows.Layout) (data : ℕ → ℕ → Bool)
    (alloc : ReportAllocation a.before a.after banks l cs q) (seed : PreparedReportInput pub m cs q description)
    (input : CellPacket.WordsAt (readings m) l.headers (cs.flatMap ReportCell.headerWords))
    (r : Returns prepareCellReports pub mac s m) (i : Fin cs.length) (c : Fin a.fragments.cells) :
    let mem := r.val.2.2
    let rows := (assignedReportReturnEquiv seed mac s).symm r
    let row := rows.val[i.val]'(i.isLt.trans_eq rows.length.symm)
    c.val=row.number →
    readings mem (f.host.cells+2*c.val+1)=row.external →
    readings mem (f.supplied+c.val)=row.supplied →
    banks.bankStart=a.cube.cellBank → banks.stride=a.cube.cellStride →
    SparseExterior.Ordered row.supplied 0 (Diagonal.ExternalSew.Fragments.spans (f.stream (readings mem)) data c.val) →
    (∀ span ∈ Diagonal.ExternalSew.Fragments.spans (f.stream (readings mem)) data c.val, span.Reads mem) →
    (SparseExterior.encode row.supplied row.bits 0
      (Diagonal.ExternalSew.Fragments.spans (f.stream (readings mem)) data c.val)).length≤a.fragments.stride →
    FragmentRows.SparseCell a f mem data i.val := by
  intro mem rows row num addr width start stride ordered sources extent
  let e := assignedReportReturnEquiv seed mac s
  let tape := (reportAssignmentEquiv cs).symm rows
  have same : cellsOfTape cs tape=rows.val := congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply rows)
  have alloc' : ReportAllocation a.before a.after banks l (cellsOfTape cs tape) q := alloc.tape _ _
  rw [same] at alloc'
  have recv := alloc'.receiving row (List.getElem_mem _)
  have read := returned_report_binding alloc seed r ⟨i.val,i.isLt.trans_eq rows.length.symm⟩
  have six := returned_report_header alloc seed input r i
  refine ⟨c,row.bits,?_,?_,?_,?_,?_,width ▸ ordered,sources,?_,width ▸ extent⟩
  · rw [addr,recv.1,CellBanks.Layout.bank,start,stride,num]
  · rw [width,ReportCell.bits_length,←stride]
    exact recv.2
  · simpa only [Nat.add_zero,ReportCell.headerWords,List.getElem_cons_zero,num] using six ⟨0,(by decide : 0<6)⟩
  · rw [width]
    exact six ⟨2,(by decide : 2<6)⟩
  · rw [←alloc.widths,num,ReportCell.bits_length]
    exact read.width
  · intro j hj
    rw [addr,width]
    change readings mem (row.external+row.supplied+j)=row.bits[j].toNat
    have bits : CellPacket.WordsAt (readings mem) (row.external+row.supplied) (row.bits.map Bool.toNat) := read.bits
    simpa only [List.getElem_map] using bits ⟨j,by simpa using hj⟩

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
