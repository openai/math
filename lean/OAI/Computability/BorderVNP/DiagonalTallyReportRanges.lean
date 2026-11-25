import OAI.Computability.BorderVNP.DiagonalTallyReportWrites
import OAI.Computability.BorderVNP.DiagonalTallyReportBatchCost

/-! # Cursor advances and occupied physical intervals of report preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open Packing.BottomReports

/-- The number of compact packed source scalars in a list of genuine original bundles. -/
def packedWords (bs : List ReportBundle) := (bs.map fun b => 1+3*b.positions.length).sum

/-- Scalar length of the emitted supplemental checker rows for these genuine bundles. -/
def supplementWords (bs : List ReportBundle) := (bs.map fun b => 9*b.positions.length+6).sum

/-- Both cursor increments count actual emitted scalar words. -/
theorem bundle_fold_fields (bs : List ReportBundle) (q : LocalReportCursor) :
    let e := bs.foldl LocalReportCursor.advance q
    e.packed=q.packed+packedWords bs ∧ e.refs=q.refs+weightedCopies bs ∧
      e.descriptors=q.descriptors+5*weightedCopies bs ∧ e.supplement=q.supplement+supplementWords bs := by
  induction bs generalizing q with
  | nil => simp [packedWords,weightedCopies,supplementWords]
  | cons b bs ih =>
    dsimp only [List.foldl_cons]
    obtain ⟨p,r,d,s⟩ := ih (q.advance b)
    simp only [LocalReportCursor.advance,ReportCursor.afterBundle] at p r d s
    simp only [packedWords,weightedCopies,supplementWords,List.map_cons,List.sum_cons,Nat.mul_add]
    simp only [LocalReportCursor.advance,ReportCursor.afterBundle] at ⊢
    simp only [packedWords,weightedCopies,supplementWords] at p r d s
    omega

/-- Global streams after the count writer and every original bundle of one cell. -/
theorem cell_after_fields {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) :
    (c.after q).packed=q.packed+packedWords c.bundles ∧
    (c.after q).refs=q.refs+l.gadgets*l.countWidth+weightedCopies c.bundles ∧
    (c.after q).descriptors=q.descriptors+5*(l.gadgets+weightedCopies c.bundles) := by
  obtain ⟨p,r,d,_⟩ := bundle_fold_fields c.bundles (c.localStart q)
  rw [← c.global_end q]
  exact ⟨p,r,by simpa [ReportCell.localEnd,ReportCell.localStart,ReportCursor.afterCounts,Nat.mul_add,Nat.add_assoc] using d⟩

/-- Total compact source-word stream of the selected team. -/
def teamPacked {l : ReportLayout} (cs : List (ReportCell l)) := (cs.map fun c => packedWords c.bundles).sum

/-- The actual terminal global cursors, including the fixed count block for every owned cell. -/
theorem cells_fold_fields {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) :
    let e := cs.foldl (fun a c => c.after a) q
    e.packed=q.packed+teamPacked cs ∧ e.refs=q.refs+cs.length*(l.gadgets*l.countWidth)+teamWeighted cs ∧
      e.descriptors=q.descriptors+5*(cs.length*l.gadgets+teamWeighted cs) := by
  induction cs generalizing q with
  | nil => simp [teamPacked,teamWeighted]
  | cons c cs ih =>
    dsimp only [List.foldl_cons]
    obtain ⟨p,r,d⟩ := ih (c.after q)
    obtain ⟨cp,cr,cd⟩ := cell_after_fields c q
    simp only [teamPacked,teamWeighted,List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.mul_add]
    simp only [teamPacked,teamWeighted,Nat.mul_add] at p r d
    rw [Nat.mul_add] at cd
    omega

/-- Half-open containment of the entire store block, allowing zero-word arrays. -/
def ReportWrite.within (s : ReportWrite) (a b : ℕ) := a ≤ s.address ∧ s.address+s.data.length ≤ b

private theorem row_length (b : ReportBundle) (q : LocalReportCursor) :
    ((b.rows q).flatMap CellSparse.Packet.record).length=9*b.positions.length+6 := by
  rw [ReportBundle.rows,List.flatMap_append,List.length_append,Writer.Frame.rows_words_length]
  simp [Writer.Frame.zeroRow,
    CellSparse.Packet.record,CellSparse.Packet.port]

/-- The four physical output streams over a contiguous sequence of original bundles. -/
def bundleRange (q e : LocalReportCursor) (s : ReportWrite) :=
  s.within q.packed e.packed ∨ s.within q.refs e.refs ∨
    s.within q.descriptors e.descriptors ∨ s.within q.supplement e.supplement

theorem bundle_write_range (b : ReportBundle) (l : ReportLayout) (q : LocalReportCursor)
    (s : ReportWrite) (hs : s∈b.writes l q) : bundleRange q (q.advance b) s := by
  simp only [ReportBundle.writes,operandWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with (rfl|rfl)|(rfl|rfl)
  · exact Or.inl ⟨le_rfl,by simp [LocalReportCursor.advance,ReportCursor.afterBundle,TallySidecar.fields_length]; omega⟩
  · exact Or.inr (Or.inr (Or.inr ⟨le_rfl,by rw [row_length]; change q.supplement+(9*b.positions.length+6) ≤ q.supplement+9*b.positions.length+6; omega⟩))
  · exact Or.inr (Or.inl ⟨le_rfl,by simp [ReportBundle.frame,DiagonalTallyOperandArray.Frame.nrefs,
      LocalReportCursor.advance,ReportCursor.afterBundle,ReportBundle.useCount]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨le_rfl,by simp [ReportBundle.frame,DiagonalTallyOperandArray.Frame.nrows,
      LocalReportCursor.advance,ReportCursor.afterBundle,ReportBundle.useCount]⟩))

theorem bundleWrites_range (l : ReportLayout) (bs : List ReportBundle) (q : LocalReportCursor)
    (s : ReportWrite) (hs : s∈bundleWrites l bs q) :
    bundleRange q (bs.foldl LocalReportCursor.advance q) s := by
  induction bs generalizing q with
  | nil => simp [bundleWrites] at hs
  | cons b bs ih =>
    rw [bundleWrites,List.mem_append] at hs
    simp only [List.foldl_cons]
    obtain ⟨p,r,d,a⟩ := bundle_fold_fields bs (q.advance b)
    rcases hs with hb|ht
    · have h := bundle_write_range b l q s hb
      unfold bundleRange ReportWrite.within at h ⊢
      omega
    · have h := ih (q.advance b) ht
      unfold bundleRange ReportWrite.within at h ⊢
      have hp : q.packed ≤ (q.advance b).packed := by change _ ≤ q.packed+1+3*b.positions.length; omega
      have hr : q.refs ≤ (q.advance b).refs := Nat.le_add_right ..
      have hd : q.descriptors ≤ (q.advance b).descriptors := Nat.le_add_right ..
      have ha : q.supplement ≤ (q.advance b).supplement := by change _ ≤ q.supplement+9*b.positions.length+6; omega
      omega

/-- The three globally contiguous output streams shared by all cells of one owner. -/
def cursorRange (q e : ReportCursor) (s : ReportWrite) :=
  s.within q.packed e.packed ∨ s.within q.refs e.refs ∨ s.within q.descriptors e.descriptors

/-- All other stores lie in the true global cell's supplemental rows, counter pair,
width word or freshly guessed tail of the receiving bank. -/
def cellRange {l : ReportLayout} (c : ReportCell l) (s : ReportWrite) :=
  let a := l.supplement+c.number*l.supplementStride
  s.within a (a+supplementWords c.bundles) ∨ s.within (l.counters+2*c.number) (l.counters+2*c.number+2) ∨
    s.within (l.tailWidths+c.number) (l.tailWidths+c.number+1) ∨
    s.within (c.external+c.supplied) (c.external+c.supplied+c.tailWidth)

theorem cell_write_range {l : ReportLayout} (c : ReportCell l) (q : ReportCursor)
    (s : ReportWrite) (hs : s∈c.writes q) : cursorRange q (c.after q) s ∨ cellRange c s := by
  obtain ⟨p,r,d⟩ := cell_after_fields c q
  simp only [ReportCell.writes,List.mem_append] at hs
  rcases hs with (hc|hb)|hf
  · simp only [operandWrites,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl <;> left
    · apply Or.inr; apply Or.inl
      simp [ReportWrite.within,ReportCell.countFrame,DiagonalTallyOperandArray.Frame.nrefs,r]
    · apply Or.inr; apply Or.inr
      simp [ReportWrite.within,ReportCell.countFrame,DiagonalTallyOperandArray.Frame.nrows,d,Nat.mul_add]
  · have h := bundleWrites_range l c.bundles (c.localStart q) s hb
    obtain ⟨_,_,_,a⟩ := bundle_fold_fields c.bundles (c.localStart q)
    change bundleRange (c.localStart q) (c.localEnd q) s at h
    change (c.localEnd q).supplement=(c.localStart q).supplement+supplementWords c.bundles at a
    simp only [bundleRange,c.global_end q,ReportCell.localStart,ReportCursor.afterCounts,a] at h
    unfold cursorRange cellRange ReportWrite.within at *
    omega
  · right
    simp only [ReportCell.finalWrites,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl <;> simp [cellRange,ReportWrite.within,c.bits_length]

/-- Each store from the whole chronological preparation belongs to an actual owned
cell or to one of the three persistent arrays between its initial and final cursors. -/
theorem cellWrites_range {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor)
    (s : ReportWrite) (hs : s∈cellWrites cs q) :
    cursorRange q (cs.foldl (fun a c => c.after a) q) s ∨ ∃ c∈cs, cellRange c s := by
  induction cs generalizing q with
  | nil => simp [cellWrites] at hs
  | cons c cs ih =>
    simp only [cellWrites,List.mem_append] at hs
    simp only [List.foldl_cons]
    obtain ⟨p,r,d⟩ := cell_after_fields c q
    obtain ⟨ep,er,ed⟩ := cells_fold_fields cs (c.after q)
    rcases hs with hc|ht
    · rcases cell_write_range c q s hc with h|h
      · left; unfold cursorRange ReportWrite.within at h ⊢; omega
      · exact Or.inr ⟨c,List.mem_cons_self,h⟩
    · rcases ih (c.after q) ht with h|⟨v,hv,h⟩
      · left; unfold cursorRange ReportWrite.within at h ⊢; omega
      · exact Or.inr ⟨v,.tail _ hv,h⟩

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
