import OAI.Computability.BorderVNP.DiagonalSignedLookupRegions
import OAI.Computability.BorderVNP.RoutingISASignedPrepReportAllocation
import OAI.Computability.BorderVNP.RoutingISASignedPrepReportRows
import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenReadback
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedTaskSource

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Signed table IDs survive every actual local report assignment -/

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalTallyAllocation DiagonalTallyMaterialize DiagonalTallyRAM

variable {w : ℕ} {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}

/-- A cell publishes its guessed tail inside its receive bank. All remaining
report writes start in the pre-task or later descriptor allocation. -/
theorem ReportAllocation.bank_or_pre (h : ReportAllocation pre post banks l cs q)
    (seg : ReportWrite) (hs : seg ∈ cellWrites cs q) :
    seg.address+seg.data.length ≤ banks.bankStart+banks.cells*banks.stride ∨ pre.start ≤ seg.address := by
  rcases cellWrites_range cs q seg hs with streams|⟨c,hc,r⟩
  · right
    have a : pre.start ≤ pre.limit := by rw [pre.footprint]; omega
    have b := h.preBefore
    have p : post.start ≤ post.packed := by
      simp only [AfterTasks.packed,AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]; omega
    have t : post.packed ≤ post.refs := by unfold AfterTasks.refs; omega
    have u : post.refs ≤ post.descriptors := by unfold AfterTasks.descriptors; omega
    simp only [cursorRange,h.initial,ReportWrite.within] at streams
    omega
  · obtain ⟨base,room⟩ := h.receiving c hc
    have ordinal := Nat.mul_le_mul_right banks.stride (h.bankNumber c hc)
    rw [Nat.succ_mul] at ordinal
    change c.external = banks.bankStart+c.number*banks.stride at base
    simp only [cellRange,ReportWrite.within,h.widths,h.supplement,h.counters,
      BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.tailWidths] at r
    omega

/-- All reported assignments, including rows later rejected by their cells,
preserve each protected primary, incoming packet or fixed-deck operand. -/
theorem ReportAllocation.read_before_tasks (h : ReportAllocation pre post banks l cs q)
    {m : Memory w} {pub : Arg → Word w} {description : ℕ}
    (seed : PreparedReportInput pub m cs q description) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (r : Returns prepareCellReports pub mac s m) (addr : ℕ)
    (clear : addr ≠ l.frame+35) (early : addr<banks.bankStart ∨
      (banks.bankStart+banks.cells*banks.stride ≤ addr ∧ addr<pre.start)) :
    r.val.2.2 addr=m addr := by
  let E := assignedReportReturnEquiv seed mac s
  let rows := E.symm r
  let tape := (reportAssignmentEquiv cs).symm rows
  have same : cellsOfTape cs tape = rows.val := congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply rows)
  have actual : ReportAllocation pre post banks l rows.val q := same ▸ h.tape _ _
  have image := (assignedReportReturnEquiv_spec seed mac s rows).2
  change readings (E (E.symm r)).val.2.2=_ at image
  rw [E.apply_symm_apply,prepareWrites_image] at image
  apply Fin.ext
  change readings r.val.2.2 addr=readings m addr
  rw [image]
  apply writes_outside
  intro seg hs
  rcases List.mem_append.mp hs with cell|last
  · have lo := actual.aboveBankStart seg cell
    have gap := actual.bank_or_pre seg cell
    omega
  · rcases List.mem_singleton.mp last with rfl
    change addr<l.frame+35 ∨ l.frame+35+1 ≤ addr
    omega

end DiagonalTallyCellReports

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM FiniteEvaluator DiagonalTallyAllocation DiagonalTallyCellReports
open RoutingISA.Evaluator BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    (a : Layout) (owner : Fin a.cube.header.d → ℕ) (team demand : ℕ)
    (A : Data a.cube.n a.cube.header.d a.cube.header.blocks a.cube.b a.cube.h a.cube.K a.cube.s)
local notation "X" => gadgetLookup a pub owner team demand A
local notation "deckEnd" => CubeConstants.arenaEnd a.cube.stop a.id

/-- At every actual report return the fixed cube ID, selected references, and
all their source words are the ones recovered on the original owned return. -/
theorem wordPrepared_on_reports (V : SignedPrep.Visits a.id pub mac s m)
    (H : OpenSuffix.Inputs)
    (prepared : CubePacket.WordPrepared X a.id pub V.owned.val.2.2)
    (packet : A.packetBase=a.cube.header.packetBase)
    (primary : (pub 0).val+112 ≤ a.cube.header.packetBase)
    (placement : OpenSuffix.Placement H a.cube a.before (pub 0).val (readings V.owned.val.2.2))
    (ready : OpenSuffix.Ready H (pub 0).val (readings V.owned.val.2.2) w)
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {banks : CellBanks.Layout} {description : ℕ}
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after banks l cs q)
    (frame : l.frame=(pub 0).val) (start : banks.bankStart=a.cube.cellBank)
    (count : banks.cells=a.cube.cells) (stride : banks.stride=a.cube.cellStride) :
    CubePacket.WordPrepared X a.id pub V.reports.val.2.2 := by
  have past : a.cube.stop ≤ deckEnd := by simp only [CubeConstants.arenaEnd,CubeConstants.idBase]; omega
  have locus {j : ℕ} (read : CubePacket.ReadAt X pub j) := gadgetLookup_readAt a pub owner team demand A packet read
  have controls := OpenSuffix.placed_words H a.cube a.before deckEnd X ready placement V.controls.property
    primary past a.constants_le_before (fun _ => locus)
  apply CubePacket.WordPrepared.transfer X prepared
  intro addr read
  refine Eq.trans (alloc.read_before_tasks seed mac _ V.reports addr ?_ ?_) (controls addr read)
  · rcases locus read with ⟨j,hj,rfl⟩ | h | h
    · simp only [CubePacket.frameWords,List.mem_cons,List.not_mem_nil,or_false] at hj
      omega
    · omega
    · have headEnd := alloc.frameBefore
      have banksEnd := a.literal_bounds.1
      omega
  · rcases locus read with ⟨j,hj,rfl⟩ | h | h
    · left
      have hr := alloc.frameBefore
      simp only [CubePacket.frameWords,List.mem_cons,List.not_mem_nil,or_false] at hj
      omega
    · exact Or.inl (start ▸ h.2)
    · right
      rw [start,count,stride,a.literal_bounds.1]
      exact ⟨h.1,h.2.trans_le a.constants_le_before⟩

end RoutingISA.SignedTaskArena

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalTallyAllocation DiagonalTallyMaterialize DiagonalTallyRAM

variable {w : ℕ} {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {a : SignedTaskArena.Layout} {banks : CellBanks.Layout}
    (alloc : ReportAllocation a.before a.after banks l cs q)

include alloc

/-- Reads of a report operand occupy a receive bank, an allocated supplement
word, or a post-task descriptor word. None intersects the fragment tables. -/
theorem ReportAllocation.signedOperand_region (addr : ℕ) (read : operandReads q.descriptors (cellOperands cs q) addr)
    (start : banks.bankStart=a.cube.cellBank) (count : banks.cells=a.cube.cells) (stride : banks.stride=a.cube.cellStride)
    (zero : l.zeroAddr=a.cube.stop) :
    a.cube.cellBank ≤ addr ∧ (addr<a.fragments.start ∨ (a.fragments.limit≤addr ∧ addr<a.before.merged) ∨
      a.after.start≤addr) := by
  have cubeEnd := a.literal_bounds
  have zeroLo : banks.bankStart+banks.cells*banks.stride ≤ l.zeroAddr := by rw [start,count,stride,zero,cubeEnd.1]
  have zeroHi : l.zeroAddr<a.before.start := by rw [zero]; omega
  have loc := alloc.read_extent zeroLo zeroHi read
  have pp : a.after.start ≤ a.after.packed := by
    simp only [AfterTasks.packed,AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]; omega
  have base : a.fragments.limit=a.before.start := rfl
  have low : a.cube.stop < a.fragments.start := by
    change a.cube.stop < CubeConstants.arenaEnd a.cube.stop a.id
    simp only [CubeConstants.arenaEnd,CubeConstants.idBase]
    omega
  refine ⟨start ▸ loc.1,?_⟩
  rcases cell_reads_covered cs q addr read with ⟨seg,hs,lo,hi⟩|rfl
  · have disjoint := alloc.bank_or_pre seg hs
    rw [start,count,stride,cubeEnd.1] at disjoint
    rcases loc.2.1 with small|big <;> omega
  · omega

variable {m : Memory w} {pub : Arg → Word w} {description : ℕ}
    (seed : PreparedReportInput pub m cs q description) (mac : TeamOpcode.Macros w 8) (s : Bank w)

/-- The true guessed owned-cell report supplies the exact descriptor inputs
and their count on its returning memory, for every possible proposed report. -/
theorem receivedOperands (r : Returns prepareCellReports pub mac s m)
    (start : banks.bankStart=a.cube.cellBank) (count : banks.cells=a.cube.cells) (stride : banks.stride=a.cube.cellStride)
    (zeroAddr : l.zeroAddr=a.cube.stop) (zero : (m l.zeroAddr).val=0) (wpos : 0<w)
    (dim : l.parameters+l.gadgets ≤ 2^w) (width : l.countWidth ≤ w)
    (source : ∀ c∈cs, ∀ b∈c.bundles, ∀ p∈b.positions, p.parameter<2^w ∧ p.place<w) :
    let rr := cellsOfTape cs ((reportReturnEquiv seed mac s).symm r)
    supplied r.val.2.2 (cellEnd rr q) q.descriptors (cellOperands rr q) ∧
      (r.val.2.2 ((pub 0).val+35)).val=(cellOperands rr q).length := by
  let E := reportReturnEquiv seed mac s
  intro rr
  have lo : banks.bankStart+banks.cells*banks.stride ≤ l.zeroAddr := by rw [start,count,stride,zeroAddr,a.literal_bounds.1]
  have hi : l.zeroAddr<a.before.start := zeroAddr ▸ (Nat.le_add_right a.cube.stop 1).trans_lt a.literal_bounds.2
  have got := reportReturnEquiv_supplied alloc seed mac s (E.symm r) lo hi zero wpos dim width source
  have post := (reportReturnEquiv_spec seed mac s (E.symm r)).2.2
  change supplied (E (E.symm r)).val.2.2 _ _ _ at got
  change readings (E (E.symm r)).val.2.2=_ at post
  rw [E.apply_symm_apply] at got post
  refine ⟨got,?_⟩
  change readings r.val.2.2 ((pub 0).val+35)=_
  rw [seed.framePointer,post,Function.update_self]

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
