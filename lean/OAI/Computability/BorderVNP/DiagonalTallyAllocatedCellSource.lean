import OAI.Computability.BorderVNP.DiagonalTallyReportAllocatedWrites
import OAI.Computability.BorderVNP.DiagonalTallyReportOperandBounds
import OAI.Computability.BorderVNP.DiagonalTallyCubeOperands

/-! # Reading the native sparse input stream from its actual physical allocations -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalTallyRAM DiagonalTallyMaterialize DiagonalTallyAllocation

variable {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}

/-- The first address following the genuine compact cell descriptor stream. -/
def cellEnd {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) := q.descriptors+5*(cellOperands cs q).length

theorem cellEnd_fold {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) :
    (cs.foldl (fun a c => c.after a) q).descriptors=cellEnd cs q := by
  induction cs generalizing q with
  | nil => simp [cellEnd,cellOperands]
  | cons c cs ih =>
    simp [cellEnd,cellOperands,List.foldl_cons,ih,c.after_descriptors,Nat.mul_add,Nat.add_assoc]

/-- The literal and the finite cube tables between the host receiving banks and the
pre-task scratch are untouched by every actual report store. -/
theorem ReportAllocation.fixedWord (h : ReportAllocation pre post banks l cs q)
    (z : ℕ) (lower : banks.bankStart+banks.cells*banks.stride ≤ z) (to_ : z<pre.start) :
    ∀ s∈prepareWrites cs q,z<s.address ∨ s.address+s.data.length ≤ z := by
  intro s hs
  rw [prepareWrites,List.mem_append] at hs
  rcases hs with hw|last
  · rcases cellWrites_range cs q s hw with stream|⟨c,hc,cell⟩
    · have pp : pre.start ≤ pre.limit := by rw [pre.footprint]; omega
      have rr : post.packed ≤ post.refs := by unfold AfterTasks.refs; omega
      have dd : post.refs ≤ post.descriptors := by unfold AfterTasks.descriptors; omega
      have ss : post.start ≤ post.packed := by
        simp only [AfterTasks.packed,AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]; omega
      have e := h.preBefore
      simp only [cursorRange,ReportWrite.within,h.initial] at stream
      omega
    · obtain ⟨base,room⟩ := h.receiving c hc
      have num : c.number<banks.cells := h.bankNumber c hc
      have bound := Nat.mul_le_mul_right banks.stride num
      rw [Nat.succ_mul] at bound
      have s₁ : pre.start ≤ pre.supplement := Nat.le_add_right ..
      have s₂ : pre.supplement ≤ pre.counters := Nat.le_add_right ..
      simp only [cellRange,ReportWrite.within,base,CellBanks.Layout.bank,h.widths,BeforeTasks.tailWidths,
        h.supplement,h.counters] at cell
      omega
  · obtain rfl := List.mem_singleton.mp last
    right
    have earlier := h.frameBefore
    simp
    omega

/-- Any actual cell operand word is past the frame, outside the typed-task windows and
cube-ID outputs, and strictly below the first word of the subsequently appended cube suffix. -/
theorem ReportAllocation.read_extent (h : ReportAllocation pre post banks l cs q)
    (zeroLo : banks.bankStart+banks.cells*banks.stride ≤ l.zeroAddr) (zeroHi : l.zeroAddr<pre.start)
    {a : ℕ} (read : operandReads q.descriptors (cellOperands cs q) a) :
    banks.bankStart ≤ a ∧ (a<pre.merged ∨ post.packed ≤ a) ∧ a<cellEnd cs q := by
  have p₁ : pre.start ≤ pre.merged := by
    simp only [BeforeTasks.merged,BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.tailWidths]; omega
  have p₂ : pre.merged ≤ pre.limit := by
    simp only [BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.six,BeforeTasks.four]; omega
  have p₃ : post.start ≤ post.descriptors := by
    simp only [AfterTasks.descriptors,AfterTasks.refs,AfterTasks.packed,AfterTasks.ids,AfterTasks.lookupRefs,
      AfterTasks.lookupRows]; omega
  have p₄ : post.descriptors ≤ cellEnd cs q := by simp [cellEnd,h.initial]
  have between := h.preBefore
  rcases cell_reads_covered cs q a read with ⟨s,hs,lo,hi⟩|rfl
  · have before := h.aboveBankStart s hs
    have middle := h.outsideMiddle s hs
    have end_ := h.write_zone s hs
    rw [cellEnd_fold] at end_
    omega
  · omega

/-- Immediately after real report preparation, the entire consecutive input is valid up
to its own first unused descriptor address. Only the actual immutable field and place
bounds enter the calculation of shifted increments. -/
theorem ReportAllocation.supplied (h : ReportAllocation pre post banks l cs q)
    {w : ℕ} (m mt : Memory w)
    (image : readings mt=Function.update (cellImages cs q (readings m)) (l.frame+35) (cellOperands cs q).length)
    (zeroLo : banks.bankStart+banks.cells*banks.stride ≤ l.zeroAddr) (zeroHi : l.zeroAddr<pre.start)
    (zero : (m l.zeroAddr).val=0) (wpos : 0<w) (dim : l.parameters+l.gadgets ≤ 2^w) (width : l.countWidth ≤ w)
    (source : ∀ c∈cs,∀ b∈c.bundles,∀ p∈b.positions,p.parameter<2^w ∧ p.place<w) :
    DiagonalTallyMaterialize.supplied mt (cellEnd cs q) q.descriptors (cellOperands cs q) := by
  obtain ⟨_,refs,_⟩ := h.ends
  have desc : post.descriptors ≤ cellEnd cs q := by simp [cellEnd,h.initial]
  have before := before_of_read_extent cs q (cellEnd cs q) (fun _ r => (h.read_extent zeroLo zeroHi r).2.2)
    (refs.le.trans desc)
  exact supplied_after_prepare cs q m mt _ image h.prepareWrites_pairwise zero (h.fixedWord l.zeroAddr zeroLo zeroHi)
    le_rfl (fun o mem => ⟨before o mem,cell_fits cs q w wpos dim width source o mem⟩)

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
