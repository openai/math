import OAI.Computability.BorderVNP.DiagonalTallyPrivateCallSource

/-! # Complete materializer input after appending the owned cube vertices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalTallyAllocation DiagonalTallyRAM DiagonalTallyMaterialize

open private reads_ofFn from OAI.Computability.BorderVNP.DiagonalTallyReportReadExtent

variable {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}

/-- The allocated descriptor count pays exactly one per cell gadget and weighted copy. -/
theorem cellOperand_count_exact {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) :
    (cellOperands cs q).length=cs.length*l.gadgets+teamWeighted cs := by
  have end_ := (cells_fold_fields cs q).2.2
  rw [cellEnd_fold,cellEnd] at end_
  omega

theorem ReportAllocation.cellCount (h : ReportAllocation pre post banks l cs q) :
    (cellOperands cs q).length ≤ post.bound.cells*post.bound.gadgets+post.bound.uses := by
  have len : cs.length ≤ post.bound.cells := h.postCells ▸ h.owned_le
  rw [cellOperand_count_exact,h.gadgets]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ len) h.uses

/-- Every five-word descriptor of an owned vertex and every pointer it reaches lies
above the frame's tally pointers, including the slot-82 pointer to literal one. -/
theorem packet_reads_high (f : DiagonalTallyCubeSuffix.Frame)
    (dir trueAddr : ℕ) (ids : Fin f.count → ℕ) (p : ℕ)
    (idLo : dir+45 ≤ f.ids) (zeroLo : dir+45 ≤ f.zeroAddr) (oneLo : dir+45 ≤ trueAddr)
    (rowLo : dir+45 ≤ p) {a : ℕ} (read : operandReads p (f.packetOperands dir trueAddr ids) a) : dir+45 ≤ a := by
  have single {i : Fin f.count} {p' : ℕ} (pp : dir+45 ≤ p')
      (r : operandReads p' [packetOperand f.parameters (f.ids+i.val) f.zeroAddr (dir+82) trueAddr (ids i)] a) :
      dir+45 ≤ a := by
    simp only [operandReads,packetOperand,List.length_cons,List.length_nil,Nat.zero_add,List.mem_singleton,
      exists_eq_left,or_false] at r
    omega
  obtain ⟨i,r⟩ := reads_ofFn p a _ read
  exact single (by omega) r

/-- Read back the cell descriptors and the actual selected vertex IDs in the memory
returned by the native suffix program. Its terminal count fits the fixed alignment
reservation, and none of its source words is a frame pointer rewritten by allocation. -/
theorem ReportAllocation.fullSource {w : ℕ} (h : ReportAllocation pre post banks l cs q)
    (m mt : Memory w) (trueAddr : ℕ) {count : ℕ} (ids : Fin count → ℕ) (vertices : count ≤ post.bound.vertices)
    (zeroLo : banks.bankStart+banks.cells*banks.stride ≤ l.zeroAddr) (zeroHi : l.zeroAddr<pre.start)
    (oneLo : banks.bankStart ≤ trueAddr) (oneHi : trueAddr<pre.start)
    (old : DiagonalTallyMaterialize.supplied m (cellEnd cs q) q.descriptors (cellOperands cs q))
    (literalPtr : (m (l.frame+82)).val=trueAddr) (zeroValue : (m l.zeroAddr).val=0)
    (trueValue : (m trueAddr).val=1) (selected : ∀ i : Fin count,(m (post.ids+i.val)).val=ids i)
    (coordFit : ∀ i, l.parameters+ids i<2^w) (wpos : 0<w)
    (image : readings mt=(post.suffixFrame (cellOperands cs q).length count l.zeroAddr l.parameters).image
      l.frame (readings m)) :
    let cells := cellOperands cs q
    let f := post.suffixFrame cells.length count l.zeroAddr l.parameters
    let os := cells++f.packetOperands l.frame trueAddr ids
    DiagonalTallyMaterialize.supplied mt post.fresh post.descriptors os ∧
      (mt (l.frame+35)).val=os.length ∧ os.length ≤ post.bound.operands ∧
      ∀ a, operandReads post.descriptors os a → outsidePointers l.frame a ∧ a≠l.frame+34 := by
  intro cells f os
  have row : q.descriptors=post.descriptors := h.initial ▸ rfl
  have start : f.start=cellEnd cs q := by simp [f,cells,DiagonalTallyCubeSuffix.Frame.start,AfterTasks.suffixFrame,cellEnd,row]
  have old' : DiagonalTallyMaterialize.supplied m f.start f.descriptors cells := by
    rw [start]
    change DiagonalTallyMaterialize.supplied m (cellEnd cs q) post.descriptors (cellOperands cs q)
    rwa [← row]
  have bef := h.frameBefore
  have ext := h.bankBefore
  have limit : pre.start ≤ pre.limit := by rw [pre.footprint]; omega
  have middle := h.preBefore
  have dst : post.start ≤ f.ids := by
    simp only [f,AfterTasks.suffixFrame,AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]; omega
  have ⟨space,sep⟩ := post.suffix_room h.cellCount vertices l.zeroAddr l.parameters
  change f.start+5*count<post.fresh at space
  change f.ids+count<f.start at sep
  have noRead {a : ℕ} (read : operandReads f.descriptors cells a) : banks.bankStart ≤ a :=
    (h.read_extent zeroLo zeroHi (by simpa [f,AfterTasks.suffixFrame,row] using read)).1
  obtain ⟨source,countRead⟩ := f.supplied_after_append m mt l.frame post.fresh trueAddr cells ids image rfl old'
    (fun _ read => by have := noRead read; omega) (by omega) (by omega) sep.le
    (by change l.zeroAddr<f.start; omega) (by omega) (by change l.zeroAddr≠l.frame+35; omega) (by omega)
    literalPtr zeroValue trueValue selected space.le coordFit wpos
  refine ⟨source,?_,?_,?_⟩
  · simpa only [os,List.length_append] using countRead
  · simp only [os,DiagonalTallyCubeSuffix.Frame.packetOperands,List.length_append,List.length_ofFn]
    exact Nat.add_le_add h.cellCount vertices
  · intro a read
    rw [reads_append] at read
    have high : l.frame+45 ≤ a := by
      rcases read with first|packet
      · have := noRead first
        omega
      · apply packet_reads_high f l.frame trueAddr ids (post.descriptors+5*cells.length) (by omega)
          (by change l.frame+45 ≤ l.zeroAddr; omega) (by omega) _ packet
        change l.frame+45 ≤ f.start
        omega
    simp only [outsidePointers]
    omega

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
