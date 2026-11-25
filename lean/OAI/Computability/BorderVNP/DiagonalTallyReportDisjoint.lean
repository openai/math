import OAI.Computability.BorderVNP.DiagonalTallyReportRanges

/-! # Separation of chronological writes into the four bundle streams and cell banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open Packing.BottomReports

/-- Order of the four stream partitions over this range of original bundles. -/
def bundleOrdered (q e : LocalReportCursor) :=
  e.supplement ≤ q.packed ∧ e.packed ≤ q.refs ∧ e.refs ≤ q.descriptors

private theorem bundle_step_mono (q : LocalReportCursor) (b : ReportBundle) :
    q.supplement ≤ (q.advance b).supplement ∧ q.packed ≤ (q.advance b).packed ∧
      q.refs ≤ (q.advance b).refs ∧ q.descriptors ≤ (q.advance b).descriptors := by
  simp only [LocalReportCursor.advance,ReportCursor.afterBundle]
  omega

private theorem bundle_step_apart (l : ReportLayout) (q : LocalReportCursor) (b : ReportBundle)
    (h : bundleOrdered q (q.advance b)) : (b.writes l q).Pairwise ReportWrite.apart := by
  have len : ((b.rows q).flatMap CellSparse.Packet.record).length=9*b.positions.length+6 := by
    rw [ReportBundle.rows,List.flatMap_append,List.length_append,Writer.Frame.rows_words_length]
    simp [Writer.Frame.zeroRow,CellSparse.Packet.record,CellSparse.Packet.port]
  simp only [bundleOrdered,LocalReportCursor.advance,ReportCursor.afterBundle] at h
  simp only [ReportBundle.writes,operandWrites,List.cons_append,List.nil_append,List.pairwise_cons,
    List.mem_cons,List.not_mem_nil,or_false,List.Pairwise.nil,and_true,forall_eq_or_imp,
    forall_eq,false_implies,implies_true]
  simp only [ReportWrite.apart,ReportBundle.frame,DiagonalTallyOperandArray.Frame.nrows,
    DiagonalTallyOperandArray.Frame.nrefs,List.length_ofFn,TallySidecar.fields_length,len,ReportBundle.useCount] at *
  omega

/-- All bundle output blocks are pairwise disjoint once their actual four terminal
cursors fit before the next physical banks. -/
theorem bundleWrites_pairwise (l : ReportLayout) (bs : List ReportBundle) (q : LocalReportCursor)
    (h : bundleOrdered q (bs.foldl LocalReportCursor.advance q)) :
    (bundleWrites l bs q).Pairwise ReportWrite.apart := by
  induction bs generalizing q with
  | nil => simp [bundleWrites]
  | cons b bs ih =>
    simp only [List.foldl_cons,bundleOrdered] at h
    obtain ⟨p,r,d,a⟩ := bundle_fold_fields bs (q.advance b)
    have mono := bundle_step_mono q b
    rw [bundleWrites,List.pairwise_append]
    refine ⟨bundle_step_apart l q b (by unfold bundleOrdered; omega),
      ih (q.advance b) (by unfold bundleOrdered; omega),?_⟩
    intro s hs t ht
    have x := bundle_write_range b l q s hs
    have y := bundleWrites_range l bs (q.advance b) t ht
    unfold bundleRange ReportWrite.within at x y
    unfold ReportWrite.apart
    omega

/-- Every indexed bank used by this cell lies below the next shared partition. -/
def ReportCell.banksOrdered {l : ReportLayout} (c : ReportCell l) (packed : ℕ) :=
  c.external+c.supplied+c.tailWidth ≤ l.tailWidths ∧ l.tailWidths+c.number+1 ≤ l.supplement ∧
    l.supplement+c.number*l.supplementStride+supplementWords c.bundles ≤ l.counters ∧
    l.counters+2*c.number+2 ≤ packed

/-- The guess interval and supplemental reservation of two genuine distinct cells
are disjoint, along with their width and counter words. -/
def ReportCell.banksApart {l : ReportLayout} (c d : ReportCell l) :=
  (c.external+c.supplied+c.tailWidth ≤ d.external+d.supplied ∨
    d.external+d.supplied+d.tailWidth ≤ c.external+c.supplied) ∧
  (l.supplement+c.number*l.supplementStride+supplementWords c.bundles ≤ l.supplement+d.number*l.supplementStride ∨
    l.supplement+d.number*l.supplementStride+supplementWords d.bundles ≤ l.supplement+c.number*l.supplementStride) ∧
  c.number ≠ d.number

private theorem count_ranges {l : ReportLayout} (c : ReportCell l) (q : ReportCursor)
    (s : ReportWrite) (h : s∈operandWrites (c.countFrame q) .count) :
    s.within q.refs (c.localStart q).refs ∨ s.within q.descriptors (c.localStart q).descriptors := by
  simp only [operandWrites,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl <;> simp [ReportWrite.within,ReportCell.localStart,ReportCursor.afterCounts,
    ReportCell.countFrame,DiagonalTallyOperandArray.Frame.nrows,DiagonalTallyOperandArray.Frame.nrefs]

private theorem final_ranges {l : ReportLayout} (c : ReportCell l) (q : LocalReportCursor)
    (s : ReportWrite) (h : s∈c.finalWrites q) :
    s.within (l.counters+2*c.number) (l.counters+2*c.number+2) ∨
    s.within (l.tailWidths+c.number) (l.tailWidths+c.number+1) ∨
    s.within (c.external+c.supplied) (c.external+c.supplied+c.tailWidth) := by
  simp only [ReportCell.finalWrites,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl <;> simp [ReportWrite.within,c.bits_length]

private theorem one_cell_pairwise {l : ReportLayout} (c : ReportCell l) (q : ReportCursor)
    (bounds : c.banksOrdered q.packed)
    (separate : (c.after q).packed ≤ q.refs ∧ (c.after q).refs ≤ q.descriptors) :
    (c.writes q).Pairwise ReportWrite.apart := by
  obtain ⟨p,r,d⟩ := cell_after_fields c q
  have ⟨ep,er,ed,ea⟩ := bundle_fold_fields c.bundles (c.localStart q)
  change (c.localEnd q).supplement=(c.localStart q).supplement+supplementWords c.bundles at ea
  have hp : (c.localEnd q).packed=(c.after q).packed := congrArg ReportCursor.packed (c.global_end q)
  have hr : (c.localEnd q).refs=(c.after q).refs := congrArg ReportCursor.refs (c.global_end q)
  have hd : (c.localEnd q).descriptors=(c.after q).descriptors := congrArg ReportCursor.descriptors (c.global_end q)
  unfold ReportCell.banksOrdered at bounds
  have bp : (bundleWrites l c.bundles (c.localStart q)).Pairwise ReportWrite.apart :=
    bundleWrites_pairwise _ _ _ (by
      change bundleOrdered (c.localStart q) (c.localEnd q)
      simp only [bundleOrdered,hp,hr,ea,ReportCell.localStart,ReportCursor.afterCounts]
      omega)
  have cp : (operandWrites (c.countFrame q) .count).Pairwise ReportWrite.apart := by
    simp [operandWrites,ReportWrite.apart,ReportCell.countFrame,DiagonalTallyOperandArray.Frame.nrefs,
      DiagonalTallyOperandArray.Frame.nrows]
    omega
  have fp : (c.finalWrites (c.localEnd q)).Pairwise ReportWrite.apart := by
    simp [ReportCell.finalWrites,ReportWrite.apart,c.bits_length]
    omega
  simp only [ReportCell.writes,List.pairwise_append]
  refine ⟨⟨cp,bp,?_⟩,fp,?_⟩
  · intro s hs t ht
    have x := count_ranges c q s hs
    have y := bundleWrites_range l c.bundles (c.localStart q) t ht
    change bundleRange (c.localStart q) (c.localEnd q) t at y
    simp only [bundleRange,hp,hr,hd,ea,ReportCell.localStart,ReportCursor.afterCounts,ReportWrite.within] at x y
    unfold ReportWrite.apart
    omega
  · intro s hs t ht
    have y := final_ranges c (c.localEnd q) t ht
    unfold ReportWrite.within at y
    unfold ReportWrite.apart
    rcases List.mem_append.mp hs with h|h
    · have x := count_ranges c q s h
      simp only [ReportWrite.within,ReportCell.localStart,ReportCursor.afterCounts] at x
      omega
    · have x := bundleWrites_range l c.bundles (c.localStart q) s h
      change bundleRange (c.localStart q) (c.localEnd q) s at x
      simp only [bundleRange,hp,hr,hd,ea,ReportCell.localStart,ReportCursor.afterCounts,ReportWrite.within] at x
      omega

/-- The global streams advance monotonically across cells. The four cell-indexed
partitions can be visited in any order with distinct receiving-bank and cell ordinals. -/
theorem cellWrites_pairwise {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor)
    (bank : ∀ c∈cs, c.banksOrdered q.packed) (distinct : cs.Pairwise ReportCell.banksApart)
    (ordered : let e := cs.foldl (fun a c => c.after a) q; e.packed ≤ q.refs ∧ e.refs ≤ q.descriptors) :
    (cellWrites cs q).Pairwise ReportWrite.apart := by
  induction cs generalizing q with
  | nil => simp [cellWrites]
  | cons c cs ih =>
    obtain ⟨bc,br⟩ := List.forall_mem_cons.mp bank
    obtain ⟨dc,dr⟩ := List.pairwise_cons.mp distinct
    dsimp only [List.foldl_cons] at ordered
    obtain ⟨p,r,d⟩ := cell_after_fields c q
    obtain ⟨ep,er,ed⟩ := cells_fold_fields cs (c.after q)
    rw [cellWrites,List.pairwise_append]
    refine ⟨one_cell_pairwise c q bc (by omega),ih (c.after q) (fun v hv => ?_) dr (by omega),?_⟩
    · have h := br v hv
      unfold ReportCell.banksOrdered at h ⊢
      omega
    · intro s hs t ht
      have x := cell_write_range c q s hs
      have y := cellWrites_range cs (c.after q) t ht
      unfold ReportCell.banksOrdered at bc
      unfold ReportWrite.apart
      rcases y with y|⟨v,hv,y⟩
      · simp only [cursorRange,cellRange,ReportWrite.within] at x y
        omega
      · have bv := br v hv
        have different := dc v hv
        simp only [ReportCell.banksOrdered,ReportCell.banksApart] at bv different
        simp only [cursorRange,cellRange,ReportWrite.within] at x y
        omega

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
