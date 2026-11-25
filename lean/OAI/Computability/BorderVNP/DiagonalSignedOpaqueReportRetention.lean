import OAI.Computability.BorderVNP.DiagonalNativeReportBindingReadback
import OAI.Computability.BorderVNP.CellPacketSources

/-! # Received original descriptions survive arbitrary signed report choices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalTallyAllocation CellPacket CellSparse CellSparse.Packet.Source

variable {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}

/-- Every report store is disjoint from an original descriptor byte following
the sampled tail in the receiving cell. The allocation places every other
cell's stores in its own stride; a cell without a report also satisfies this. -/
theorem ReportAllocation.opaque_word (alloc : ReportAllocation pre post banks l cs q)
    (c : Fin banks.cells) (start : ℕ) (j : ℕ) (room : start+j<banks.stride)
    (reserved : ∀ row∈cs, row.number=c.val → row.supplied+row.tailWidth ≤ start) :
    ∀ z∈prepareWrites cs q, banks.bank c.val+start+j<z.address ∨ z.address+z.data.length≤banks.bank c.val+start+j := by
  have lim := Nat.mul_le_mul_right banks.stride c.isLt
  rw [Nat.succ_mul] at lim
  have before := alloc.bankBefore
  have loc : banks.bank c.val+start+j<pre.start := by dsimp only [CellBanks.Layout.bank]; omega
  have frame := alloc.frameBefore
  have mid : pre.start≤pre.limit := by rw [pre.footprint]; omega
  have packed : post.start≤post.packed ∧ post.packed≤post.refs ∧ post.refs≤post.descriptors := by
    simp only [AfterTasks.descriptors,AfterTasks.refs,AfterTasks.packed,AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]
    omega
  intro z hz
  rw [prepareWrites,List.mem_append] at hz
  rcases hz with body|last
  · rcases cellWrites_range cs q z body with stream|⟨other,ho,hc⟩
    · simp only [cursorRange,ReportWrite.within,alloc.initial] at stream
      left
      have := alloc.preBefore
      omega
    · rcases hc with supp|counters|width|tail
      · left
        have bound := supp.1
        rw [alloc.supplement] at bound
        simp only [BeforeTasks.supplement,BeforeTasks.tailWidths] at bound
        omega
      · left
        have bound := counters.1
        rw [alloc.counters] at bound
        simp only [BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.tailWidths] at bound
        omega
      · left
        have bound := width.1
        rw [alloc.widths] at bound
        change pre.start+other.number≤z.address at bound
        omega
      · obtain ⟨left,right⟩ := tail
        obtain ⟨addr,size⟩ := alloc.receiving other ho
        rcases lt_trichotomy other.number c.val with early|same|later
        · have ord := Nat.mul_le_mul_right banks.stride early
          rw [Nat.succ_mul] at ord
          simp only [CellBanks.Layout.bank] at addr ⊢
          right; omega
        · have tailLength := reserved other ho same
          rw [same] at addr
          right; omega
        · have ord := Nat.mul_le_mul_right banks.stride later
          rw [Nat.succ_mul] at ord
          simp only [CellBanks.Layout.bank] at addr ⊢
          left; omega
  · obtain rfl := List.mem_singleton.mp last
    right
    change l.frame+35+1≤banks.bank c.val+start+j
    simp only [CellBanks.Layout.bank]
    omega

/-- Every actual returning count/use history retains the opaque verifier
header and body already delivered into this receiver's bank. -/
theorem returned_opaque {w description packet : ℕ} {pub : Arg → Word w} {m : Memory w}
    {mac : TeamOpcode.Macros w 8} {s : Bank w} (alloc : ReportAllocation pre post banks l cs q)
    (seed : PreparedReportInput pub m cs q description) (r : Returns prepareCellReports pub mac s m)
    (c : Fin banks.cells) (start head : ℕ) (fs : List Factor)
    (room : start+packet≤banks.stride)
    (tail : ∀ row∈cs, row.number=c.val → row.supplied+row.tailWidth ≤ start)
    (delivered : Delivered (description:=packet) (readings m) (banks.bank c.val+start) head fs) :
    Delivered (description:=packet) (readings r.val.2.2) (banks.bank c.val+start) head fs := by
  let equiv := assignedReportReturnEquiv seed mac s
  let rows := equiv.symm r
  let bits := (reportAssignmentEquiv cs).symm rows
  have same : cellsOfTape cs bits=rows.val := congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply rows)
  have actual : ReportAllocation pre post banks l rows.val q := same ▸ alloc.tape _ _
  have tailsFit (row : ReportCell l) (member : row ∈ rows.val) (number : row.number=c.val) : row.supplied+row.tailWidth ≤ start := by
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp member
    let i : Fin cs.length := Fin.cast rows.length j
    have eqn := rows.row_eq i
    have hn := congrArg ReportCell.number eqn
    have hw := congrArg ReportCell.supplied eqn
    have ht := congrArg ReportCell.tailWidth eqn
    simp only [ReportCell.withTape_tailWidth] at ht
    exact (congrArg₂ Nat.add hw ht).le.trans (tail cs[i.val] (List.getElem_mem _) (hn.symm.trans number))
  have image := (assignedReportReturnEquiv_spec seed mac s rows).2
  rw [show assignedReportReturnEquiv seed mac s rows=r from equiv.apply_symm_apply r,prepareWrites_image] at image
  intro j used
  rw [image]
  exact (writes_outside _ _ _ (actual.opaque_word c start j.val (by have := j.isLt; omega) tailsFit)).trans (delivered j used)

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
