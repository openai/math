import OAI.Computability.BorderVNP.RoutingISAScheduleClockReports
import OAI.Computability.BorderVNP.CellTeamReportCharge

/-! # Supplemental records and counts after a native report return

The report pass writes one binding for each original marked position and
one padding binding per retained site. Each cell's two counters describe
the exact consecutive scalar array left at its allocated supplemental address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator CellSparse CellSparse.Packet CellPacket Packing.BottomReports
open private append_words from OAI.Computability.BorderVNP.CellPacketSupplementalMemory
open private row_length from OAI.Computability.BorderVNP.DiagonalTallyReportRanges
open private bundleCursor_tape from OAI.Computability.BorderVNP.RoutingISAScheduleClockReports

private theorem previous_count (bs : List ReportBundle) (q : LocalReportCursor) :
    (bs.foldl LocalReportCursor.advance q).previousRows=q.previousRows+(bindingRows bs q).length := by
  have nrows (f : Writer.Frame) (rel : ℕ → ℕ) (n : ℕ) : (f.rows rel n).length=n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [Writer.Frame.rows,ih]
  induction bs generalizing q with
  | nil => simp [bindingRows]
  | cons b bs ih =>
    simp only [List.foldl_cons,ih,LocalReportCursor.advance,bindingRows,List.length_append,ReportBundle.rows,
      nrows,List.length_cons,List.length_nil]
    omega

private theorem bundle_words (l : ReportLayout) (bs : List ReportBundle) (q : LocalReportCursor) (m : ℕ → ℕ)
    (resident : ∀ b∈bundleWrites l bs q, WordsAt m b.address b.data) :
    WordsAt m q.supplement ((bindingRows bs q).flatMap record) := by
  induction bs generalizing q with
  | nil => exact fun i => i.elim0
  | cons b bs ih =>
    rw [bindingRows,List.flatMap_append]
    apply append_words
    · apply resident ⟨q.supplement,(b.rows q).flatMap record⟩
      exact List.mem_append_left _ (by simp [ReportBundle.writes])
    · have next := ih (q.advance b) (fun x hx => resident x (List.mem_append_right _ hx))
      simpa only [LocalReportCursor.advance,row_length,Nat.add_assoc] using next

/-- The real array of checker records and its two scalar counts at one
global cell's pre-task addresses. The cursor is the one at entry to this cell. -/
def ReportCell.SupplementStored {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) (m : ℕ → ℕ) : Prop :=
  let rows := bindingRows c.bundles (c.localStart q)
  WordsAt m (l.supplement+c.number*l.supplementStride) (rows.flatMap record) ∧
    m (l.counters+2*c.number)=rows.length ∧ m (l.counters+2*c.number+1)=(rows.flatMap record).length

private theorem cell_stored {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) (m : ℕ → ℕ)
    (resident : ∀ b∈c.writes q, WordsAt m b.address b.data) : c.SupplementStored q m := by
  have binds := bundle_words l c.bundles (c.localStart q) m (fun b hb =>
    resident b (List.mem_append_left _ (List.mem_append_right _ hb)))
  let stop := c.localEnd q
  let diff := stop.supplement-(l.supplement+c.number*l.supplementStride)
  have both := resident ⟨l.counters+2*c.number,[stop.previousRows,diff]⟩
    (List.mem_append_right _ List.mem_cons_self)
  have count : m (l.counters+2*c.number)=stop.previousRows := both ⟨0,(by decide : 0<2)⟩
  have words : m (l.counters+2*c.number+1)=diff := both ⟨1,(by decide : 1<2)⟩
  have rows := previous_count c.bundles (c.localStart q)
  have endAt := (bundle_fold_fields c.bundles (c.localStart q)).2.2.2
  change stop.previousRows=0+_ at rows
  change stop.supplement=l.supplement+c.number*l.supplementStride+supplementWords c.bundles at endAt
  refine ⟨binds,count.trans (by simpa only [Nat.zero_add] using rows),words.trans ?_⟩
  change stop.supplement-(l.supplement+c.number*l.supplementStride)=_
  rw [endAt,Nat.add_sub_cancel_left,binding_words]
  rfl

private def StoredCells {l : ReportLayout} (m : ℕ → ℕ) : List (ReportCell l) → ReportCursor → Prop
  | [],_ => True
  | c::cs,q => c.SupplementStored q m ∧ StoredCells m cs (c.after q)

private theorem stored_cells {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) (m : ℕ → ℕ)
    (resident : ∀ b∈cellWrites cs q, WordsAt m b.address b.data) : StoredCells m cs q := by
  induction cs generalizing q with
  | nil => trivial
  | cons c cs ih =>
    exact ⟨cell_stored c q m (fun x hx => resident x (List.mem_append_left _ hx)),
      ih (c.after q) (fun x hx => resident x (List.mem_append_right _ hx))⟩

private theorem stored_at {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) (m : ℕ → ℕ)
    (stored : StoredCells m cs q) (i : Fin cs.length) :
    cs[i].SupplementStored ((cs.take i.val).foldl (fun z c => c.after z) q) m := by
  induction cs generalizing q with
  | nil => exact i.elim0
  | cons c cs ih =>
    cases i using Fin.cases with
    | zero => exact stored.1
    | succ j => exact ih (c.after q) stored.2 j

private theorem binding_tape (a : ℕ → Bool) (p : ℕ) (bs : List ReportBundle) (q : LocalReportCursor) :
    bindingRows (tapeBundles a p bs) q=bindingRows bs q := by
  induction bs generalizing p q with
  | nil => rfl
  | cons b bs ih =>
    change b.rows q++bindingRows (tapeBundles a (p+b.useCount) bs) (q.advance b)=_
    rw [ih]
    rfl

private theorem stored_tape {l : ReportLayout} (a : ℕ → Bool) (p : ℕ) (cs : List (ReportCell l))
    (q : ReportCursor) (m : ℕ → ℕ) : StoredCells m (tapeCells a p cs) q ↔ StoredCells m cs q := by
  induction cs generalizing p q with
  | nil => rfl
  | cons c cs ih =>
    have tail : (c.withTape a p).after q=c.after q := bundleCursor_tape ..
    have binds : bindingRows (c.withTape a p).bundles ((c.withTape a p).localStart q)=bindingRows c.bundles (c.localStart q) :=
      binding_tape ..
    simp only [tapeCells,StoredCells,tail,ih,ReportCell.SupplementStored,binds]
    rfl

variable {w description : ℕ} {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    {pre : DiagonalTallyAllocation.BeforeTasks} {post : DiagonalTallyAllocation.AfterTasks} {banks : CellBanks.Layout}

/-- At every actual native report return the original physical cell has its
ordered binding words and exact record and scalar counts, independently of
the count digits and expanded use flags consumed by that return. -/
theorem report_return_supplement (alloc : ReportAllocation pre post banks l cs q)
    (seed : PreparedReportInput pub m cs q description) (x : Returns prepareCellReports pub mac s m)
    (i : Fin cs.length) : cs[i].SupplementStored ((cs.take i.val).foldl (fun z c => c.after z) q) (readings x.val.2.2) := by
  let tape := (reportReturnEquiv seed mac s).symm x
  let rows := cellsOfTape cs tape
  have real := (reportReturnEquiv_spec seed mac s tape).2.2
  rw [show reportReturnEquiv seed mac s tape=x from Equiv.apply_symm_apply ..,prepareWrites_image] at real
  have chosen : ReportAllocation pre post banks l rows q := alloc.tape _ _
  have stored := stored_cells rows q (readings x.val.2.2) (fun b hb => by
    rw [real]
    exact writes_readback _ _ chosen.prepareWrites_pairwise _ (List.mem_append_left _ hb))
  exact stored_at cs q _ ((stored_tape _ _ cs q _).mp stored) i

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
