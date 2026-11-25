import OAI.Computability.BorderVNP.RoutingISASignedPrepReports
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsTape
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedCellSource

/-! # Native report returns from the original physical allocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalTallyAllocation
open private tape_map from_cells from_bundles from OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsTape

variable {w description : ℕ} {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {pub : Arg → Word w} {m : Memory w} {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}

/-- Construct the finite tape bijection's physical input from the original grouped
headers, incoming private site strings, allocation and published frame words. -/
theorem ReportAllocation.preparedInput (alloc : ReportAllocation pre post banks l cs q)
    (fp : (pub 0).val=l.frame) (seeded : l.seed q cs.length (readings m))
    (data : ReportDirectory.InputData cs w description pre.bound.bundles (readings m))
    (site : SiteIntervals cs description banks.stride) (ctl : l.control+28 ≤ banks.bankStart)
    (privateEnd : ∀ c∈cs, c.privateWires+c.supplied+c.tailWidth<2^w)
    (width : l.fieldWidth ≤ w) (coords : l.parameters+l.gadgets < 2^w)
    (raw : l.fieldWidth+l.bodyCap < 2^w) (space : post.fresh < 2^w) :
    PreparedReportInput pub m cs q description := by
  have frame := alloc.frameBefore
  have banksBelow := alloc.bankBefore
  have before := alloc.preBefore
  have own := alloc.owned_le
  have low : pre.start ≤ pre.limit := by rw [pre.footprint]; omega
  have high : post.start ≤ post.fresh := by
    simp only [AfterTasks.fresh,AfterTasks.descriptors,AfterTasks.refs,AfterTasks.packed,
      AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]; omega
  have head : l.headers+6*cs.length ≤ pre.limit := by
    rw [alloc.headers,BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges]
    omega
  exact ⟨fp,alloc.initial ▸ rfl,seeded,by omega,by omega,by omega,raw,
    fun a => alloc.cellInputs_tape w description (readings m) data site ctl privateEnd width coords space a 0⟩

private theorem cell_bitWrite {l : ReportLayout} (cs : List (ReportCell l)) (c : ReportCell l)
    (hc : c∈cs) (q : ReportCursor) :
    ⟨c.external+c.supplied,c.bits.map Bool.toNat⟩ ∈ cellWrites cs q := by
  induction cs generalizing q with
  | nil => simp at hc
  | cons d ds ih =>
    rcases List.mem_cons.mp hc with rfl | tail
    · simp [cellWrites,ReportCell.writes,ReportCell.finalWrites]
    · exact List.mem_append_right _ (ih tail (d.after q))

variable (alloc : ReportAllocation pre post banks l cs q) (seed : PreparedReportInput pub m cs q description)
    (mac : TeamOpcode.Macros w 8) (s : Bank w)

include alloc

/-- For every decoded owned cell, the returned memory supplies its actual count digits
and per-copy use flags to the private checker at the assigned physical addresses. -/
theorem reportReturnEquiv_cellBits (tape : ReportTape cs) :
    let mt := (reportReturnEquiv seed mac s tape).val.2.2
    ∀ c ∈ cellsOfTape cs tape,
      (∀ g j, (mt (c.external+c.supplied+g.val*l.countWidth+j.val)).val=(c.counts g j).toNat) ∧
      useBitsAt (readings mt) (c.external+c.supplied+l.gadgets*l.countWidth) c.bundles := by
  have image := (reportReturnEquiv_spec seed mac s tape).2.2
  rw [prepareWrites_image] at image
  have assigned : ReportAllocation pre post banks l (cellsOfTape cs tape) q := alloc.tape _ _
  dsimp only
  intro c hc
  apply c.readBits (readings (reportReturnEquiv seed mac s tape).val.2.2)
  unfold literalBitsAt
  rw [image]
  exact writes_readback _ _ assigned.prepareWrites_pairwise _
    (List.mem_append_left _ (cell_bitWrite _ c hc q))

/-- The same returned memory supplies the consecutive five-word descriptor array,
its indirect count and use operands, and the addressed literals consumed by tallying. -/
theorem reportReturnEquiv_supplied (tape : ReportTape cs)
    (zeroLo : banks.bankStart+banks.cells*banks.stride ≤ l.zeroAddr) (zeroHi : l.zeroAddr<pre.start)
    (zero : (m l.zeroAddr).val=0) (wpos : 0<w) (dim : l.parameters+l.gadgets ≤ 2^w) (width : l.countWidth ≤ w)
    (source : ∀ c∈cs, ∀ b∈c.bundles, ∀ p∈b.positions, p.parameter<2^w ∧ p.place<w) :
    let mt := (reportReturnEquiv seed mac s tape).val.2.2
    let rows := cellsOfTape cs tape
    DiagonalTallyMaterialize.supplied mt (cellEnd rows q) q.descriptors (cellOperands rows q) := by
  have assigned : ReportAllocation pre post banks l (cellsOfTape cs tape) q := alloc.tape _ _
  apply assigned.supplied _ _ (reportReturnEquiv_spec seed mac s tape).2.2 zeroLo zeroHi zero wpos dim width
  intro c hc b hb p hp
  obtain ⟨d,hd,j,rfl⟩ := from_cells _ cs 0 hc
  obtain ⟨t,ht,k,rfl⟩ := from_bundles _ d.bundles _ hb
  exact source d hd t ht p hp

omit alloc in
private theorem tapeOriginal (a : ℕ → Bool) (bs : List ReportBundle) (p : ℕ) :
    originalFields (tapeBundles a p bs)=originalFields bs := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
    simp only [tapeBundles,originalFields,List.map_cons,List.sum_cons]
    exact congrArg (fun n => 1+b.positions.length+n) (ih _)

omit alloc in
/-- A single clock, computed from the original owner metadata before any guesses,
bounds every report return. It charges the actual expanded marked occurrences. -/
theorem reportReturnEquiv_clock (tape : ReportTape cs) :
    traceCost (reportReturnEquiv seed mac s tape).val.1 ≤
      54+(79+105*l.gadgets+16*(l.gadgets*l.countWidth))*cs.length+
        129*teamOriginal cs*(l.fieldWidth+1)+131*teamWeighted cs := by
  have clock := (reportReturnEquiv_weight_cost seed mac s tape).2
  let a := fun i => if h : i < (reportBits cs).length then tape ⟨i,h⟩ else false
  change traceCost _ ≤ 54+(79+105*l.gadgets+16*(l.gadgets*l.countWidth))*(tapeCells a 0 cs).length+
    129*teamOriginal (tapeCells a 0 cs)*(l.fieldWidth+1)+131*teamWeighted (tapeCells a 0 cs) at clock
  simpa only [tapeCells_length,teamOriginal,teamWeighted,
    tape_map a (fun c => originalFields c.bundles) (fun c j => tapeOriginal _ _ _) cs 0,
    tape_map a (fun c => weightedCopies c.bundles)
      (fun c j => by simp [ReportCell.withTape,weightedCopies]) cs 0] using clock

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
