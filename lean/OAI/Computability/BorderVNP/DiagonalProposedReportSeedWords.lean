import OAI.Computability.BorderVNP.DiagonalSourceReportSparseLaunch
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsTape

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Initial six-word rows and the chronological choices of a prepared report -/

namespace DiagonalTallyCellReports

open RoutingISA DiagonalTallyAllocation

private theorem headerWordCount {l : ReportLayout} (cs : List (ReportCell l)) :
    (cs.flatMap ReportCell.headerWords).length=6*cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.flatMap_cons,List.length_append,List.length_cons,ih]
                    change 6+6*cs.length=6*(cs.length+1)
                    omega

private theorem readSourceRows {l : ReportLayout} {w desc : ℕ} (cs : List (ReportCell l))
    (q : ReportCursor) (p : ℕ) (mem : ℕ → ℕ) (inputs : cellInputs w desc cs q p mem)
    (clear : ∀ t∈cellWrites cs q, ∀ j<6*cs.length, p+j<t.address ∨ t.address+t.data.length≤p+j) :
    CellPacket.WordsAt mem p (cs.flatMap ReportCell.headerWords) := by
  induction cs generalizing q p mem with
  | nil => intro i; exact Fin.elim0 i
  | cons c cs ih =>
    have head := inputs.1.1.row
    have tail := ih (c.after q) (p+6) (c.image q mem) inputs.2 (fun t ht j hj => by
      have keep := clear t (List.mem_append_right _ ht) (6+j)
        (by simp only [List.length_cons]; omega)
      simpa only [Nat.add_assoc] using keep)
    intro i
    change mem (p+i.val)=(c.headerWords++cs.flatMap ReportCell.headerWords)[i.val]
    by_cases h : i.val<c.headerWords.length
    · simpa only [List.getElem_append_left h] using head ⟨i.val,h⟩
    · have len : c.headerWords.length=6 := rfl
      have bound : i.val-6<(cs.flatMap ReportCell.headerWords).length := by
        have hi := i.isLt
        simp only [List.flatMap_cons,List.length_append,len] at hi
        omega
      have previous := tail ⟨i.val-6,bound⟩
      have idx : p+6+(i.val-6)=p+i.val := by omega
      rw [idx] at previous
      have preserved : c.image q mem (p+i.val)=mem (p+i.val) := by
        rw [ReportCell.writes_image]
        apply writes_outside
        intro t ht
        exact clear t (List.mem_append_left _ ht) i.val
          ((headerWordCount (c::cs)) ▸ i.isLt)
      rw [preserved] at previous
      simpa only [List.getElem_append_right (Nat.le_of_not_gt h),len] using previous

private theorem sampledHeaders {l : ReportLayout} (a : ℕ → Bool) (cs : List (ReportCell l)) (p : ℕ) :
    (tapeCells a p cs).flatMap ReportCell.headerWords=cs.flatMap ReportCell.headerWords := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih => simp only [tapeCells,List.flatMap_cons,ReportCell.withTape_headerWords,ih]

open Evaluator.SignedPrep VPVNP.BurstRAM

/-- A fitted scanner reads the actual initial six-word header of every row. Its preceding rows can
write the receiving banks and the packed output, while the header address remains between them. -/
theorem _root_.OAI.Computability.BorderVNP.RoutingISA.Evaluator.SignedPrep.PreparedReportInput.physicalHeaders
    {w desc : ℕ} {pub : Arg → Word w} {mem : Memory w} {l : ReportLayout}
    {cs : List (ReportCell l)} {q : ReportCursor} (seed : PreparedReportInput pub mem cs q desc)
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    (alloc : ReportAllocation pre post banks l cs q) :
    CellPacket.WordsAt (readings mem) l.headers (cs.flatMap ReportCell.headerWords) := by
  let a : ℕ → Bool := fun _ => false
  let rows := tapeCells a 0 cs
  have h := alloc.tape a 0
  have low : pre.merged≤pre.six := by simp only [BeforeTasks.six,BeforeTasks.four]; omega
  have high : pre.six+6*pre.bound.cells≤post.packed := by
    have fit := alloc.preBefore
    simp only [BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges] at fit
    simp only [AfterTasks.packed,AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]
    omega
  have size : rows.length≤pre.bound.cells := h.owned_le
  rw [←sampledHeaders a cs 0]
  apply readSourceRows rows q l.headers (readings mem) (seed.inputs a)
  intro t ht j hj
  rcases h.write_bank_interval t ht with left|right
  · exact Or.inr (by rw [alloc.headers]; omega)
  · have after := right.1
    exact Or.inl (by rw [alloc.headers]; omega)

end DiagonalTallyCellReports

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalTallyCellReports

/-- The original report choices can be decoded with any fitted scanner on these same rows. -/
theorem ReportArgumentCut.assignmentWithSeed {w j n : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {reg : Bank w} {mem : Memory w} {ret : Returns prepareCellReports pub mac reg mem}
    {l : ReportLayout} {cs : List (ReportCell l)} {src : ReportAssignments cs} {q p : ReportCursor}
    (cut : ReportArgumentCut ret src q j) (seed : PreparedReportInput pub mem cs p n) :
    (assignedReportReturnEquiv seed mac reg).symm ret=src := by
  have observed := (reportReturnEquiv_recover seed mac reg ret).symm.trans
    (reportReturnEquiv_recover cut.seed mac reg ret)
  have same := List.ofFn_injective observed
  change reportAssignmentEquiv cs ((reportReturnEquiv seed mac reg).symm ret)=src
  rw [same]
  exact cut.assignment

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
