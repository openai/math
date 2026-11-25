import OAI.Computability.BorderVNP.DiagonalNativeReportBindings
import OAI.Computability.BorderVNP.RoutingISASignedPrepReportAllocation
import OAI.Computability.BorderVNP.CellPacketSupplementalMemory

/-! # Returned report words for the native supplemental cell splice

Each original bundle writes its binding record words at the advancing
supplement cursor. The complete traversal keeps them available, together
with their two counters and the same assignment's count and use bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalTallyAllocation CellSparse CellSparse.Packet Packing.BottomReports
open private append_words from OAI.Computability.BorderVNP.CellPacketSupplementalMemory
open private row_length from OAI.Computability.BorderVNP.DiagonalTallyReportRanges

private theorem writer_length (f : Writer.Frame) (rel : ℕ → ℕ) (n : ℕ) : (f.rows rel n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Writer.Frame.rows,ih]

private theorem final_rows (bs : List ReportBundle) (q : LocalReportCursor) :
    (bs.foldl LocalReportCursor.advance q).previousRows = q.previousRows+(bindingRows bs q).length := by
  induction bs generalizing q with
  | nil => rfl
  | cons b bs ih =>
    rw [List.foldl_cons,ih,bindingRows,List.length_append]
    simp only [LocalReportCursor.advance,ReportBundle.rows,List.length_append,List.length_singleton,writer_length]
    omega

/-- Contiguous readback across the separate native writes of the listed bundles. -/
private theorem bundle_words {l : ReportLayout} (bs : List ReportBundle) (q : LocalReportCursor)
    (mem : ℕ → ℕ) (resident : ∀ s ∈ bundleWrites l bs q, CellPacket.WordsAt mem s.address s.data) :
    CellPacket.WordsAt mem q.supplement ((bindingRows bs q).flatMap record) := by
  induction bs generalizing q with
  | nil => exact fun i => i.elim0
  | cons b bs ih =>
    rw [bindingRows,List.flatMap_append]
    have head := resident ⟨q.supplement,(b.rows q).flatMap record⟩ (by simp [bundleWrites,ReportBundle.writes])
    have rest := ih (q.advance b) (fun s hs => resident s (List.mem_append_right _ hs))
    apply append_words head
    simpa only [row_length,LocalReportCursor.advance,Nat.add_assoc] using rest

/-- At a given chronological ordinal the global cursors have traversed exactly the
preceding cells of this same assignment. -/
private theorem cell_writes_at {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor)
    (i : Fin cs.length) :
    let previous := (cs.take i.val).foldl (fun a c => c.after a) q
    ∀ s ∈ cs[i.val].writes previous, s ∈ cellWrites cs q := by
  induction cs generalizing q with
  | nil => exact i.elim0
  | cons c cs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fun s hs => List.mem_append_left _ hs
    · intro previous s hs
      apply List.mem_append_right
      exact ih (c.after q) j s hs

/-- Values in the returned physical cell, with its actual record-list and word
counts, the complete list of encoded binding records, and the compact tail. -/
structure ReportCell.BindingReadback {l : ReportLayout} (r : ReportCell l) (q : ReportCursor)
    (mem : ℕ → ℕ) : Prop where
  recordCount : mem (l.counters+2*r.number) = (bindingRows r.bundles (r.localStart q)).length
  wordCount : mem (l.counters+2*r.number+1) = ((bindingRows r.bundles (r.localStart q)).flatMap record).length
  records : CellPacket.WordsAt mem (l.supplement+r.number*l.supplementStride)
    ((bindingRows r.bundles (r.localStart q)).flatMap record)
  width : mem (l.tailWidths+r.number) = r.tailWidth
  bits : CellPacket.WordsAt mem (r.external+r.supplied) (r.bits.map Bool.toNat)

private theorem ReportCell.bindingReadback {l : ReportLayout} (r : ReportCell l) (q : ReportCursor)
    (mem : ℕ → ℕ) (resident : ∀ s ∈ r.writes q, CellPacket.WordsAt mem s.address s.data) :
    r.BindingReadback q mem := by
  let start := r.localStart q
  let finish := r.localEnd q
  let addr := l.supplement+r.number*l.supplementStride
  have count : finish.previousRows = (bindingRows r.bundles start).length := by
    simpa only [finish,ReportCell.localEnd,start,ReportCell.localStart,Nat.zero_add] using
      final_rows r.bundles start
  have words : finish.supplement - addr = ((bindingRows r.bundles start).flatMap record).length := by
    have h := (bundle_fold_fields r.bundles start).2.2.2
    change finish.supplement=addr+supplementWords r.bundles at h
    rw [h,Nat.add_sub_cancel_left,binding_words,supplementWords]
  have size : finish.external-(r.external+r.supplied)=r.tailWidth := by
    rw [show finish.external=r.external+r.supplied+r.tailWidth from r.external_end q,Nat.add_sub_cancel_left]
  have counters := resident ⟨l.counters+2*r.number,[finish.previousRows,finish.supplement-addr]⟩ (by
    simp only [ReportCell.writes,List.mem_append,ReportCell.finalWrites,List.mem_cons]
    exact .inr (.inl rfl))
  have width := resident ⟨l.tailWidths+r.number,[finish.external-(r.external+r.supplied)]⟩ (by
    simp only [ReportCell.writes,List.mem_append,ReportCell.finalWrites,List.mem_cons]
    exact .inr (.inr (.inl rfl)))
  have bits := resident ⟨r.external+r.supplied,r.bits.map Bool.toNat⟩ (by simp [ReportCell.writes,ReportCell.finalWrites])
  refine ⟨?_,?_,?_,?_,bits⟩
  · simpa only [Nat.add_zero,List.getElem_cons_zero,count] using counters ⟨0,(by decide : 0<2)⟩
  · simpa only [List.getElem_cons_succ,List.getElem_cons_zero,words] using counters ⟨1,(by decide : 1<2)⟩
  · exact bundle_words r.bundles start mem (fun s hs => resident s
      (List.mem_append_left _ (List.mem_append_right _ hs)))
  · simpa only [Nat.add_zero,List.getElem_cons_zero,size] using width ⟨0,(by decide : 0<1)⟩

/-- The selected native report return provides all supplemental fields at the
physical global cell number, for every assignment on the actual received cells. -/
theorem assignedReportReturn_bindingReadback {w description : ℕ} {l : ReportLayout}
    {cs : List (ReportCell l)} {q : ReportCursor} {pub : Arg → Word w} {m : Memory w}
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    (alloc : ReportAllocation pre post banks l cs q) (seed : PreparedReportInput pub m cs q description)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (rows : ReportAssignments cs) (i : Fin rows.val.length) :
    let mem := (assignedReportReturnEquiv seed mac s rows).val.2.2
    let previous := (rows.val.take i.val).foldl (fun a c => c.after a) q
    rows.val[i.val].BindingReadback previous (readings mem) := by
  intro mem previous
  let tape := (reportAssignmentEquiv cs).symm rows
  have same : cellsOfTape cs tape = rows.val :=
    congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply rows)
  have assigned : ReportAllocation pre post banks l (cellsOfTape cs tape) q := alloc.tape _ _
  rw [same] at assigned
  have image := (assignedReportReturnEquiv_spec seed mac s rows).2
  rw [prepareWrites_image] at image
  apply ReportCell.bindingReadback
  intro z hz
  change CellPacket.WordsAt (readings (assignedReportReturnEquiv seed mac s rows).val.2.2) _ _
  rw [image]
  exact writes_readback _ _ assigned.prepareWrites_pairwise _
    (List.mem_append_left _ (cell_writes_at rows.val q i z hz))

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
