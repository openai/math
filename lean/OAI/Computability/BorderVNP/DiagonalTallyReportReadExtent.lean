import OAI.Computability.BorderVNP.DiagonalTallyReportResident
import OAI.Computability.BorderVNP.DiagonalTallyRAMAllocatedRun

/-! # Locating every word probed by an emitted cell operand -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open RoutingISA DiagonalTallyRAM DiagonalTallyMaterialize DiagonalTallyOperandArray TallySidecar

/-- A concrete word in one of the actual successive native write ranges. -/
def writtenWord (ws : List ReportWrite) (a : ℕ) :=
  ∃ w∈ws, w.address ≤ a ∧ a<w.address+w.data.length

private theorem writtenWord_mem {xs ys : List ReportWrite} {a : ℕ} (h : writtenWord xs a)
    (subset : ∀ x∈xs,x∈ys) : writtenWord ys a := by
  obtain ⟨x,hx,lo,hi⟩ := h
  exact ⟨x,subset x hx,lo,hi⟩

/-- Splitting a physical operand stream retains the starting pointer of the second part. -/
theorem reads_append (p a : ℕ) (xs ys : List Operand) :
    operandReads p (xs++ys) a ↔ operandReads p xs a ∨ operandReads (p+5*xs.length) ys a := by
  induction xs generalizing p with
  | nil => simp [operandReads]
  | cons o os ih =>
    simp only [List.cons_append,operandReads,ih,List.length_cons,Nat.mul_succ]
    rw [show p+(5*os.length+5)=p+5+5*os.length by omega]
    simp only [or_assoc]

private theorem reads_ofFn {n : ℕ} (p a : ℕ) (os : Fin n → Operand) (read : operandReads p (List.ofFn os) a) :
    ∃ i, operandReads (p+5*i.val) [os i] a := by
  induction n generalizing p with
  | zero => simp [operandReads] at read
  | succ n ih =>
    rw [List.ofFn_succ,← List.singleton_append,reads_append] at read
    rcases read with head|tail
    · exact ⟨0,by simpa using head⟩
    · obtain ⟨i,hi⟩ := ih (p+5) (fun i => os i.succ) (by simpa using tail)
      exact ⟨i.succ,by simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hi⟩

private theorem descriptor_word (f : DiagonalTallyOperandArray.Frame) (k : Kind) {a : ℕ} (lo : f.descriptors ≤ a)
    (hi : a<f.descriptors+5*f.nrows k) : writtenWord (operandWrites f k) a :=
  ⟨⟨f.descriptors,List.ofFn fun i : Fin (5*f.nrows k) => f.field k i.val⟩,
    by simp [operandWrites],lo,by simpa using hi⟩

private theorem reference_word (f : DiagonalTallyOperandArray.Frame) (k : Kind) {a : ℕ} (lo : f.refs ≤ a)
    (hi : a<f.refs+f.nrefs k) : writtenWord (operandWrites f k) a :=
  ⟨⟨f.refs,List.ofFn fun i : Fin (f.nrefs k) => f.refValue k i.val⟩,
    by simp [operandWrites],lo,by simpa using hi⟩

private theorem count_reads {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) (a : ℕ)
    (read : operandReads q.descriptors (List.ofFn fun g => (c.countFrame q).countRow g (c.counts g)) a) :
    writtenWord (operandWrites (c.countFrame q) .count) a ∨ a=l.zeroAddr ∨
      c.external+c.supplied ≤ a ∧ a<c.external+c.supplied+l.gadgets*l.countWidth := by
  obtain ⟨g,hg⟩ := reads_ofFn _ _ _ read
  have gi := g.isLt
  change g.val<l.gadgets at gi
  have endG := Nat.mul_le_mul_right l.countWidth gi
  rw [Nat.succ_mul] at endG
  simp only [operandReads,Frame.countRow,Frame.countDigits,List.length_reverse,List.length_ofFn,
    List.mem_reverse,List.mem_ofFn,or_false,ReportCell.countFrame] at hg
  rcases hg with d|z|z|r|⟨p,⟨j,rfl⟩,rfl⟩
  · left
    apply descriptor_word _ .count
    · change q.descriptors ≤ a; omega
    · change a<q.descriptors+5*l.gadgets; omega
  · exact .inr (.inl z)
  · exact .inr (.inl z)
  · left
    apply reference_word _ .count
    · change q.refs ≤ a; omega
    · change a<q.refs+l.gadgets*l.countWidth; omega
  · right; right
    have ji := j.isLt
    change c.external+c.supplied ≤ c.external+c.supplied+g.val*l.countWidth+j.val ∧
      c.external+c.supplied+g.val*l.countWidth+j.val<c.external+c.supplied+l.gadgets*l.countWidth
    omega

private theorem unary_reads (l : ReportLayout) (b : ReportBundle) (q : LocalReportCursor) (a : ℕ)
    (read : operandReads q.descriptors (List.ofFn (b.operand q.toReportCursor q.external)) a) :
    writtenWord (b.writes l q) a ∨ q.external ≤ a ∧ a<q.external+b.useCount := by
  obtain ⟨i,h⟩ := reads_ofFn _ _ _ read
  have hi := i.isLt
  have hb : 0<b.header.copies := by
    by_contra! bad
    have z : b.header.copies=0 := by omega
    simp [ReportBundle.useCount,z] at hi
  have j : i.val/b.header.copies<b.positions.length := (Nat.div_lt_iff_lt_mul hb).mpr hi
  simp only [operandReads,ReportBundle.operand,unaryOperand,List.length_cons,List.length_nil,
    List.mem_singleton,exists_eq_left,or_false,Nat.zero_add] at h
  let f := b.frame l q.toReportCursor q.external
  have sub {x : ℕ} (e : writtenWord (operandWrites f .unary) x) : writtenWord (b.writes l q) x :=
    writtenWord_mem e fun _ hx => List.mem_append_right _ hx
  have src {x : ℕ} (lo : q.packed ≤ x) (hi : x<q.packed+1+3*b.positions.length) : writtenWord (b.writes l q) x :=
    ⟨⟨q.packed,fields b.positions⟩,List.mem_append_left _ List.mem_cons_self,lo,by simpa [fields_length,Nat.add_assoc] using hi⟩
  rcases h with d|p|p|r|e
  · left; apply sub; apply descriptor_word f .unary
    · change q.descriptors ≤ a; omega
    · change a<q.descriptors+5*b.useCount; omega
  · left; exact src (by omega) (by omega)
  · left; exact src (by omega) (by omega)
  · left; apply sub; apply reference_word f .unary
    · change q.refs ≤ a; omega
    · change a<q.refs+b.useCount; omega
  · right; change q.external+i.val=a at e; omega

private theorem use_reads (l : ReportLayout) (bs : List ReportBundle) (q : LocalReportCursor) (a : ℕ)
    (read : operandReads q.descriptors (bundleOperands bs q.toReportCursor q.external) a) :
    writtenWord (bundleWrites l bs q) a ∨ q.external ≤ a ∧ a<q.external+weightedCopies bs := by
  induction bs generalizing q with
  | nil => exact False.elim read
  | cons b bs ih =>
    rw [bundleOperands,reads_append] at read
    simp only [List.length_ofFn] at read
    have amount : weightedCopies (b::bs)=b.useCount+weightedCopies bs := rfl
    rw [amount]
    rcases read with h|h
    · rcases unary_reads l b q a h with h|h
      · exact .inl (writtenWord_mem h fun _ hx => List.mem_append_left _ hx)
      · right; omega
    · rcases ih (q.advance b) h with h|h
      · exact .inl (writtenWord_mem h fun _ hx => List.mem_append_right _ hx)
      · change q.external+b.useCount ≤ a ∧ a<q.external+b.useCount+weightedCopies bs at h
        right; omega

/-- Every indirect or descriptor word read for this owned cell was actually written by
its preparation, except the separately installed constant zero. -/
theorem ReportCell.reads_covered {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) (a : ℕ)
    (read : operandReads q.descriptors (c.operands q) a) : writtenWord (c.writes q) a ∨ a=l.zeroAddr := by
  have fromBits (lo : c.external+c.supplied ≤ a) (hi : a<c.external+c.supplied+c.tailWidth) :
      writtenWord (c.writes q) a :=
    ⟨⟨c.external+c.supplied,c.bits.map Bool.toNat⟩,
      List.mem_append_right _ (by simp [finalWrites]),lo,by simpa [c.bits_length] using hi⟩
  rw [operands,reads_append] at read
  rcases read with h|h
  · rcases count_reads c q a h with h|h|h
    · exact .inl (writtenWord_mem h fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx))
    · exact .inr h
    · exact .inl (fromBits h.1 (by unfold tailWidth; omega))
  · simp only [List.length_ofFn] at h
    rcases use_reads l c.bundles (c.localStart q) a h with h|h
    · exact .inl (writtenWord_mem h fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx))
    · change c.external+c.supplied+l.gadgets*l.countWidth ≤ a ∧
        a<c.external+c.supplied+l.gadgets*l.countWidth+weightedCopies c.bundles at h
      exact .inl (fromBits (by omega) (by simpa [tailWidth,weightedCopies,Nat.add_assoc] using h.2))

/-- Concrete coverage for the entire native input stream, enabling preservation through
the separate typed-task windows and generated cube-ID output interval. -/
theorem cell_reads_covered {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) (a : ℕ)
    (read : operandReads q.descriptors (cellOperands cs q) a) : writtenWord (cellWrites cs q) a ∨ a=l.zeroAddr := by
  induction cs generalizing q with
  | nil => exact False.elim read
  | cons c cs ih =>
    rw [cellOperands,reads_append] at read
    rcases read with h|h
    · rcases c.reads_covered q a h with h|h
      · exact .inl (writtenWord_mem h fun _ hx => List.mem_append_left _ hx)
      · exact .inr h
    · rw [← c.after_descriptors] at h
      rcases ih (c.after q) h with h|h
      · exact .inl (writtenWord_mem h fun _ hx => List.mem_append_right _ hx)
      · exact .inr h

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
