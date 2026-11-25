import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsDirectory
import OAI.Computability.BorderVNP.DiagonalTallyReportOwnedAllocation

/-! # Allocating the true compact owner rows of the native report directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.ReportDirectory

open DiagonalTallyAllocation RoutingISA TypedTaskBuilder Packing.BundleDirectory

/-- The address column produced by the receiving-bank installer is indexed by the
same global cell number used by the compact owner scan. -/
theorem writtenBankAddresses (banks : CellBanks.Layout) (rows : CellControlRows.Layout) (raw : ℕ → ℕ)
    (C : ℕ) (base : rows.banks=banks.dest) (cells : C ≤ banks.cells) (c : Fin C) :
    banks.written raw banks.cells (rows.banks+2*c.val+1)=banks.bank c.val := by
  rw [base]
  exact (banks.written_at raw (c.isLt.trans_le cells)).2

/-- The actual six-word owner directory, including its original supplied-width
column and stable bottom rows, meets all persistent report allocation bounds. -/
theorem allocation_le (pre : BeforeTasks) (post : AfterTasks) (banks : CellBanks.Layout)
    (d : Packing.BundleDirectory.Layout) (rows : CellControlRows.Layout)
    (frame control h H body zeroAddr : ℕ)
    (bind : Bindings pre d rows (reportLayout pre post frame control h H body zeroAddr))
    (owner : Fin d.bundles → Fin d.cells) (source : Fin d.bundles → ReportBundle)
    (raw : ℕ → ℕ) (counts : ℕ → Fin post.bound.gadgets → Fin post.bound.countWidth → Bool)
    (physical : d.cells ≤ banks.cells) (bankCells : banks.cells ≤ pre.bound.cells) (postCells : post.bound.cells=pre.bound.cells)
    (frameBefore : frame+96 ≤ banks.bankStart) (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start)
    (preBefore : pre.limit ≤ post.start) (bankTable : rows.banks+2*d.cells ≤ pre.start)
    (offsetTable : rows.offsets+2*rows.cables+d.cells ≤ pre.start)
    (bankWords : ∀ c : Fin d.cells, raw (rows.banks+2*c.val+1)=banks.bank c.val)
    (receiveRoom : ∀ c : Fin d.cells, raw (rows.offsets+2*rows.cables+c.val)+
      (post.bound.gadgets*post.bound.countWidth+weightedCopies ((sourceRows owner c.val).map source)) ≤ banks.stride)
    (supp : ∀ c : Fin d.cells, supplementWords ((sourceRows owner c.val).map source) ≤ pre.bound.supplementStride)
    (bundleLimit : d.bundles ≤ post.bound.bundles) (marks : ∀ r, (source r).positions.length ≤ post.bound.marked)
    (copies : (∑ r, (source r).useCount) ≤ post.bound.uses) :
    let l := reportLayout pre post frame control h H body zeroAddr
    let mem := grouped d owner source raw
    ReportAllocation pre post banks l (directoryCells d rows l owner source mem counts) post.reportCursor := by
  intro l mem
  let cs := directoryCells d rows l owner source mem counts
  let team (i : Fin d.cells) := rows.owner mem i.val
  have len : cs.length=rows.before mem rows.cells := List.length_ofFn
  let e := (finCongr len).trans ((ownedOrder rows.toLayout mem).symm.trans
    (Equiv.subtypeEquiv (p := fun c : Fin rows.cells => rows.owner mem c.val=rows.team)
      (q := fun c : Fin d.cells => team c=rows.team) (finCongr bind.cells) (fun _ => Iff.rfl)))
  have cell (i : Fin cs.length) :
      cs[i]=directoryCell d rows l owner source mem counts (e i).val.val := by
    have hi : i.val < rows.before mem rows.cells := len ▸ i.isLt
    change (directoryCells d rows l owner source mem counts)[i.val] = _
    simp only [directoryCells,List.getElem_ofFn,globalCell,dite_eq_left hi]
    rfl
  have low (a : ℕ) (ha : a<pre.start) : mem a=raw a := by
    have rl : pre.start ≤ pre.ranges := by
      simp only [BeforeTasks.ranges,BeforeTasks.six,BeforeTasks.four,BeforeTasks.merged,
        BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.tailWidths]
      omega
    have ol : pre.ranges ≤ pre.bundleTable := Nat.le_add_right ..
    exact d.image_outside _ _ _ _ (Or.inl (ha.trans_le (rl.trans bind.ranges.ge)))
      (Or.inl (ha.trans_le (rl.trans (ol.trans bind.output.ge))))
  apply ReportAllocation.of_sourceRows_le pre post banks frame control h H body zeroAddr cs owner team
    rows.team e source (fun i => congrArg ReportCell.number (cell i))
    (fun i => congrArg ReportCell.bundles (cell i)) physical bankCells postCells frameBefore bankBefore preBefore
    _ supp bundleLimit marks copies
  intro c hc
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hc
  let i : Fin cs.length := ⟨j,hj⟩
  change cs[i].external=banks.bank cs[i].number ∧ cs[i].supplied+cs[i].tailWidth ≤ banks.stride
  rw [cell i]
  let n := (e i).val
  have hn := n.isLt
  have bank := low (rows.banks+2*n.val+1) (by omega)
  have offset := low (rows.offsets+2*rows.cables+n.val) (by omega)
  exact ⟨bank.trans (bankWords n),by
    change mem (rows.offsets+2*rows.cables+n.val)+
      (post.bound.gadgets*post.bound.countWidth+weightedCopies ((sourceRows owner n.val).map source)) ≤ banks.stride
    rw [offset]
    exact receiveRoom n⟩

/-- The equal-capacity report directory is a specialization of the physical allocation. -/
theorem allocation (pre : BeforeTasks) (post : AfterTasks) (banks : CellBanks.Layout)
    (d : Packing.BundleDirectory.Layout) (rows : CellControlRows.Layout)
    (frame control h H body zeroAddr : ℕ)
    (bind : Bindings pre d rows (reportLayout pre post frame control h H body zeroAddr))
    (owner : Fin d.bundles → Fin d.cells) (source : Fin d.bundles → ReportBundle)
    (raw : ℕ → ℕ) (counts : ℕ → Fin post.bound.gadgets → Fin post.bound.countWidth → Bool)
    (bankCells : banks.cells=pre.bound.cells) (postCells : post.bound.cells=pre.bound.cells)
    (frameBefore : frame+96 ≤ banks.bankStart) (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start)
    (preBefore : pre.limit ≤ post.start) (bankTable : rows.banks+2*d.cells ≤ pre.start)
    (offsetTable : rows.offsets+2*rows.cables+d.cells ≤ pre.start)
    (bankWords : ∀ c : Fin d.cells, raw (rows.banks+2*c.val+1)=banks.bank c.val)
    (receiveRoom : ∀ c : Fin d.cells, raw (rows.offsets+2*rows.cables+c.val)+
      (post.bound.gadgets*post.bound.countWidth+weightedCopies ((sourceRows owner c.val).map source)) ≤ banks.stride)
    (supp : ∀ c : Fin d.cells, supplementWords ((sourceRows owner c.val).map source) ≤ pre.bound.supplementStride)
    (bundleLimit : d.bundles ≤ post.bound.bundles) (marks : ∀ r, (source r).positions.length ≤ post.bound.marked)
    (copies : (∑ r, (source r).useCount) ≤ post.bound.uses) :
    let l := reportLayout pre post frame control h H body zeroAddr
    let mem := grouped d owner source raw
    ReportAllocation pre post banks l (directoryCells d rows l owner source mem counts) post.reportCursor :=
  allocation_le pre post banks d rows frame control h H body zeroAddr bind owner source raw counts
    (bankCells ▸ bind.cellLimit) bankCells.le postCells frameBefore bankBefore preBefore bankTable offsetTable
    bankWords receiveRoom supp bundleLimit marks copies

end DiagonalTallyCellReports.ReportDirectory

end BorderVNP
end Computability
end OAI
