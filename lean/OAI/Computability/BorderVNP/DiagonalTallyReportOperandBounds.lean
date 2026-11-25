import OAI.Computability.BorderVNP.DiagonalTallyReportRanges
import OAI.Computability.BorderVNP.DiagonalTallyReportReadExtent

/-! # Arithmetic of every emitted count and shifted-use operand -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open DiagonalTallyMaterialize DiagonalTallyRAM DiagonalTallyOperandArray

private theorem bundle_digits_end (bs : List ReportBundle) (q : ReportCursor) (external : ℕ)
    (o : Operand) (mem : o∈bundleOperands bs q external) : o.digitsAddr+o.digits.length ≤ q.refs+weightedCopies bs := by
  induction bs generalizing q external with
  | nil => simp [bundleOperands] at mem
  | cons b bs ih =>
    rw [bundleOperands,List.mem_append] at mem
    change _ ≤ q.refs+(b.useCount+weightedCopies bs)
    rcases mem with first|rest
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp first
      change q.refs+i.val+1 ≤ q.refs+(b.useCount+weightedCopies bs)
      have hi := i.isLt
      omega
    · have later := ih (q.afterBundle b) (external+b.useCount) rest
      change _ ≤ q.refs+b.useCount+weightedCopies bs at later
      omega

/-- This bound includes the empty indirect digit array of a zero-width count. -/
theorem cell_digits_end {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor)
    (o : Operand) (mem : o∈cellOperands cs q) :
    o.digitsAddr+o.digits.length ≤ (cs.foldl (fun a c => c.after a) q).refs := by
  induction cs generalizing q with
  | nil => simp [cellOperands] at mem
  | cons c cs ih =>
    rw [cellOperands,List.mem_append] at mem
    dsimp only [List.foldl_cons]
    rcases mem with first|rest
    · obtain ⟨_,next,_⟩ := cell_after_fields c q
      obtain ⟨_,last,_⟩ := cells_fold_fields cs (c.after q)
      rw [ReportCell.operands,List.mem_append] at first
      rcases first with count|use
      · obtain ⟨g,rfl⟩ := List.mem_ofFn.mp count
        have gi := g.isLt
        change g.val<l.gadgets at gi
        have mult := Nat.mul_le_mul_right l.countWidth gi
        rw [Nat.succ_mul] at mult
        simp only [Frame.countRow,Frame.countDigits,List.length_reverse,List.length_ofFn,ReportCell.countFrame]
        omega
      · have h := bundle_digits_end _ _ _ _ use
        change _ ≤ q.refs+l.gadgets*l.countWidth+weightedCopies c.bundles at h
        omega
    · exact ih (c.after q) rest

private theorem read_member {o : Operand} (p : ℕ) (os : List Operand) (mem : o∈os) (a : ℕ)
    (indirect : a=o.offsetAddr ∨ a=o.placeAddr ∨ ∃ r∈o.digits,r.1=a) : operandReads p os a := by
  induction os generalizing p with
  | nil => simp at mem
  | cons x xs ih =>
    rcases List.mem_cons.mp mem with rfl|hx
    · rcases indirect with h|h|h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inr (.inl h))))
    · exact .inr (.inr (.inr (.inr (.inr (ih (p+5) hx)))))

/-- The actual reached words and terminal reference cursor suffice for the full physical
address bound, even when an individual reference range is empty. -/
theorem before_of_read_extent {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) (limit : ℕ)
    (reads : ∀ a, operandReads q.descriptors (cellOperands cs q) a → a<limit)
    (refEnd : (cs.foldl (fun a c => c.after a) q).refs ≤ limit) :
    ∀ o∈cellOperands cs q,o.before limit := by
  intro o mem
  exact ⟨reads _ (read_member _ _ mem _ (.inl rfl)),reads _ (read_member _ _ mem _ (.inr (.inl rfl))),
    (cell_digits_end cs q o mem).trans refEnd,fun r hr => reads _ (read_member _ _ mem _ (.inr (.inr ⟨r,hr,rfl⟩)))⟩

private theorem bundle_fits (bs : List ReportBundle) (q : ReportCursor) (external w : ℕ)
    (source : ∀ b∈bs,∀ p∈b.positions,p.parameter<2^w ∧ p.place<w) :
    ∀ o∈bundleOperands bs q external,o.fits w := by
  induction bs generalizing q external with
  | nil => simp [bundleOperands]
  | cons b bs ih =>
    intro o mem
    rw [bundleOperands,List.mem_append] at mem
    rcases mem with first|rest
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp first
      have hi := source b List.mem_cons_self (b.source i) (List.getElem_mem ..)
      simp only [ReportBundle.operand,Operand.fits,unaryOperand_pair]
      refine ⟨hi.1,hi.2,?_⟩
      split
      · exact Nat.pow_lt_pow_right (by decide) hi.2
      · positivity
    · exact ih (q.afterBundle b) (external+b.useCount) (fun x hx => source x (.tail _ hx)) o rest

/-- The machine shift width and count width come from the actual one-copy records and
length controls. Each native increment fits even for an arbitrary guessed report stream. -/
theorem cell_fits {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) (w : ℕ)
    (wpos : 0<w) (dim : l.parameters+l.gadgets ≤ 2^w) (width : l.countWidth ≤ w)
    (source : ∀ c∈cs,∀ b∈c.bundles,∀ p∈b.positions,p.parameter<2^w ∧ p.place<w) :
    ∀ o∈cellOperands cs q,o.fits w := by
  induction cs generalizing q with
  | nil => simp [cellOperands]
  | cons c cs ih =>
    intro o mem
    rw [cellOperands,List.mem_append] at mem
    rcases mem with first|rest
    · rw [ReportCell.operands,List.mem_append] at first
      rcases first with count|use
      · obtain ⟨g,rfl⟩ := List.mem_ofFn.mp count
        rw [Operand.fits,(c.countFrame q).count_pair g (c.counts g)]
        have gi := g.isLt
        change g.val<l.gadgets at gi
        change l.parameters+g.val<2^w ∧ 0<w ∧ VPVNP.TapeWord.value (List.ofFn (c.counts g))<2^w
        have h := VPVNP.TapeWord.value_lt (List.ofFn (c.counts g))
        rw [List.length_ofFn] at h
        exact ⟨by omega,wpos,h.trans_le (Nat.pow_le_pow_right (by decide) width)⟩
      · exact bundle_fits _ _ _ w (source c List.mem_cons_self) o use
    · exact ih (c.after q) (fun z hz => source z (.tail _ hz)) o rest

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
