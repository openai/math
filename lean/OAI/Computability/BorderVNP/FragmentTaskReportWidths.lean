import OAI.Computability.BorderVNP.RoutingISASignedPrepReportAllocation
import OAI.Computability.BorderVNP.RoutingISASignedTaskArena

/-! # Typed task-source extents in the actual returned report memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalTallyAllocation
open private partitions bank_past_le from OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputs
open private from_cells tape_map from OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsTape

variable {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {w : ℕ}
    (alloc : ReportAllocation pre post banks l cs q)

private theorem tail_write (r : ReportCell l) (owned : r ∈ cs) (q : ReportCursor) :
    ⟨l.tailWidths+r.number,[r.tailWidth]⟩ ∈ cellWrites cs q := by
  induction cs generalizing q with
  | nil => simp at owned
  | cons d ds ih =>
    rcases List.mem_cons.mp owned with rfl | rest
    · simp [cellWrites,ReportCell.writes,ReportCell.finalWrites,r.external_end]
    · exact List.mem_append_right _ (ih rest _)

variable {old out : Memory w}
    (image : readings out=applyWrites (readings old) (prepareWrites cs q))

include alloc image in
/-- Read the genuine guessed width published for an owned cell. -/
theorem ReportAllocation.owned_tail_width (r : ReportCell l) (owned : r ∈ cs) :
    readings out (pre.tailWidths+r.number)=r.tailWidth := by
  rw [image,← alloc.widths]
  have rd := writes_readback (readings old) (prepareWrites cs q) alloc.prepareWrites_pairwise
    ⟨l.tailWidths+r.number,[r.tailWidth]⟩ (List.mem_append_left _ (tail_write r owned q))
  simpa only [Nat.add_zero,List.getElem_cons_zero] using rd ⟨0,by simp⟩

include alloc image in
/-- No guessed report from another cell changes an unowned cell's old width.
This includes the packed streams, supplemental rows, guessed bits and frame count. -/
theorem ReportAllocation.unowned_tail_width (c : Fin banks.cells)
    (unowned : ∀ r ∈ cs, r.number≠c.val) :
    readings out (pre.tailWidths+c.val)=readings old (pre.tailWidths+c.val) := by
  have parts := partitions alloc
  have lower := alloc.frameBefore
  have index := c.isLt.trans_le alloc.bankCells
  have address : pre.tailWidths+c.val < pre.supplement := Nat.add_lt_add_left index _
  have base : pre.start ≤ pre.tailWidths+c.val := Nat.le_add_right ..
  rw [image]
  apply writes_outside
  intro s hs
  rcases List.mem_append.mp hs with writes | finish
  · rcases cellWrites_range cs q s writes with stream | ⟨r,owned,inside⟩
    · simp only [cursorRange,ReportWrite.within,alloc.initial] at stream
      left; omega
    · have sep := unowned r owned
      have bankEnd := bank_past_le alloc owned
      have fits := (alloc.receiving r owned).2
      simp only [cellRange,ReportWrite.within,alloc.supplement,alloc.counters,alloc.widths] at inside
      omega
  · obtain rfl := List.mem_singleton.mp finish
    right; simp only [List.length_singleton]; omega

include alloc image in
/-- The report traversal never writes in the low public supplied-width directory. -/
theorem ReportAllocation.supply_count (a : ℕ) (frame : l.frame+35 < a) (bank : a < banks.bankStart) :
    readings out a=readings old a := by
  rw [image]
  apply writes_outside
  intro s hs
  rcases List.mem_append.mp hs with cell | finish
  · exact .inl (bank.trans_le (alloc.aboveBankStart s cell))
  · obtain rfl := List.mem_singleton.mp finish
    exact .inr frame

include alloc image in
/-- The returned task sources fit the physical receive stride at every global
cell. On owned cells the report writer supplies the new width. On unowned cells
the already initialized width and the public supplied count survive exactly. -/
theorem ReportAllocation.post_report_extents (supply : ℕ)
    (frame : l.frame+35 < supply) (below : supply+banks.cells ≤ banks.bankStart)
    (counts : ∀ r ∈ cs, readings old (supply+r.number)=r.supplied)
    (unowned : ∀ c : Fin banks.cells, (∀ r ∈ cs, r.number≠c.val) →
      readings old (supply+c.val)+readings old (pre.tailWidths+c.val) ≤ banks.stride) (c : Fin banks.cells) :
    readings out (supply+c.val)+readings out (pre.tailWidths+c.val) ≤ banks.stride := by
  have below' := Nat.add_lt_add_left c.isLt supply
  rw [alloc.supply_count image _ (by omega) (below'.trans_le below)]
  by_cases owner : ∃ r ∈ cs, r.number=c.val
  · obtain ⟨r,hr,num⟩ := owner
    rw [← num,alloc.owned_tail_width image r hr,counts r hr]
    exact (alloc.receiving r hr).2
  · have absent (r : ReportCell l) (hr : r ∈ cs) : r.number≠c.val := fun eq => owner ⟨r,hr,eq⟩
    rw [alloc.unowned_tail_width image c absent]
    exact unowned c absent

variable {arena : SignedTaskArena.Layout} {pub : Arg → Word w} {description : ℕ}

/-- For every genuinely returned tape, the task builder's source extents fit
the signed arena. Only the pre-report high bank needs to start at zero on cells
this team does not own. The original geometry supplies every public count. -/
theorem reportReturnEquiv_task_extents (assigned : ReportAllocation arena.before arena.after banks l cs q)
    (seed : PreparedReportInput pub old cs q description) (mac : TeamOpcode.Macros w 8) (reg : Bank w)
    (tape : ReportTape cs) (offsets : ℕ)
    (cells : banks.cells=arena.cube.cells) (stride : banks.stride=arena.cube.cellStride)
    (frame : l.frame+35 < offsets+2*arena.cube.cables)
    (below : offsets+2*arena.cube.cables+arena.cube.cells ≤ banks.bankStart)
    (counts : ∀ r ∈ cs, readings old (offsets+2*arena.cube.cables+r.number)=r.supplied)
    (full : ∀ c : Fin banks.cells, readings old (offsets+2*arena.cube.cables+c.val)≤banks.stride)
    (blank : ∀ c : Fin banks.cells, readings old (arena.before.tailWidths+c.val)=0)
    (c : ℕ) (hc : c < arena.cube.cells) :
    let mem := readings (reportReturnEquiv seed mac reg tape).val.2.2
    mem (offsets+2*arena.cube.cables+c)+mem (arena.before.tailWidths+c) ≤ arena.cube.cellStride := by
  intro mem
  have image := (reportReturnEquiv_spec seed mac reg tape).2.2
  rw [prepareWrites_image] at image
  let actual : ReportAllocation arena.before arena.after banks l (cellsOfTape cs tape) q := assigned.tape _ _
  rw [← stride]
  apply actual.post_report_extents image _ frame (cells ▸ below) _ _ ⟨c,cells ▸ hc⟩
  · intro r hr
    obtain ⟨d,hd,j,rfl⟩ := from_cells _ cs 0 hr
    exact counts d hd
  · intro c _
    simpa only [blank,Nat.add_zero] using full c

/-- At the native report return, bound a cell precisely when the retained
physical owner word assigns that cell to this team. Every such cell has its
own report, whose supplied and tail widths fit the receiving bank. -/
theorem reportReturnEquiv_owned_extents (assigned : ReportAllocation arena.before arena.after banks l cs q)
    (seed : PreparedReportInput pub old cs q description) (mac : TeamOpcode.Macros w 8) (reg : Bank w)
    (tape : ReportTape cs) (offsets team : ℕ)
    (stride : banks.stride=arena.cube.cellStride)
    (frame : l.frame+35 < offsets+2*arena.cube.cables)
    (below : offsets+2*arena.cube.cables+arena.cube.cells ≤ banks.bankStart)
    (hostLow : l.frame+35 < arena.cube.hostDirectory)
    (hostEnd : arena.cube.hostDirectory+2*arena.cube.cells ≤ banks.bankStart)
    (counts : ∀ r ∈ cs, readings old (offsets+2*arena.cube.cables+r.number)=r.supplied)
    (roster : ∀ c<arena.cube.cells, readings old (arena.cube.hostDirectory+2*c)=team →
      ∃ r∈cs,r.number=c) (c : ℕ) (hc : c<arena.cube.cells) :
    let mem := readings (reportReturnEquiv seed mac reg tape).val.2.2
    mem (arena.cube.hostDirectory+2*c)=team →
      mem (offsets+2*arena.cube.cables+c)+mem (arena.before.tailWidths+c) ≤ arena.cube.cellStride := by
  intro mem owns
  have image := (reportReturnEquiv_spec seed mac reg tape).2.2
  rw [prepareWrites_image] at image
  let actual : ReportAllocation arena.before arena.after banks l (cellsOfTape cs tape) q := assigned.tape _ _
  have oldOwner := (actual.supply_count image (arena.cube.hostDirectory+2*c) (by omega) (by omega)).symm.trans owns
  obtain ⟨s,hs,number⟩ := roster c hc oldOwner
  have same : (cellsOfTape cs tape).map ReportCell.number=cs.map ReportCell.number :=
    tape_map _ _ (fun _ _ => rfl) cs 0
  have numbered : c ∈ (cellsOfTape cs tape).map ReportCell.number := same ▸ List.mem_map.mpr ⟨s,hs,number⟩
  obtain ⟨r,hr,atCell⟩ := List.mem_map.mp numbered
  have supply : readings old (offsets+2*arena.cube.cables+r.number)=r.supplied := by
    obtain ⟨d,hd,j,rfl⟩ := from_cells _ cs 0 hr
    exact counts d hd
  dsimp only [mem]
  rw [←atCell,actual.supply_count image _ (by omega) (by omega),actual.owned_tail_width image r hr,supply,←stride]
  exact (actual.receiving r hr).2

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
