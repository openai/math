import OAI.Computability.BorderVNP.DiagonalNativeReportBindingReadback
import OAI.Computability.BorderVNP.RoutingISASignedPrepSourceRows
import OAI.Computability.BorderVNP.RoutingISASignedPrepReportAllocation

/-! # Actual signed report visits on the source's immutable directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalResidueRAM DiagonalTallyAllocation DiagonalTallyCellReports
open private redecode from OAI.Computability.BorderVNP.RoutingISASignedPrepReportRows
open private from_cells tape_Received from OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsTape

variable {l k : ReportLayout} {cs : List (ReportCell l)} {ds : List (ReportCell k)}
    (same : SameReportCells cs ds) {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {q : ReportCursor} {w description : ℕ} {pub : Arg → Word w} {m : Memory w}

include same

/-- Resetting or guessing different counts and uses on an otherwise
identical directory leaves the genuine allocation valid. -/
theorem SameReportCells.source_allocation (alloc : ReportAllocation pre post banks l cs q) :
    ReportAllocation pre post banks k ds q := by
  obtain ⟨layout,clear⟩ := same
  subst k
  change eraseReportBits cs=eraseReportBits ds at clear
  let z : ReportAssignments cs := ⟨ds,clear.symm⟩
  let tape := (reportAssignmentEquiv cs).symm z
  have equal : cellsOfTape cs tape=ds := congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply z)
  rw [←equal]
  exact alloc.tape _ _

/-- Every tape maps to identical chronological scanner inputs on the same
physical control RAM. The prepared source is valid before a report is chosen. -/
theorem SameReportCells.source_seed (seed : PreparedReportInput pub m cs q description) :
    PreparedReportInput pub m ds q description := by
  obtain ⟨layout,clear⟩ := same
  subst k
  change eraseReportBits cs=eraseReportBits ds at clear
  let z : ReportAssignments cs := ⟨ds,clear.symm⟩
  have length : ds.length=cs.length := z.length
  refine ⟨seed.framePointer,seed.first,by simpa only [length] using seed.seeded,seed.frameRoom,seed.controlRoom,
    by simpa only [length] using seed.headerRoom,seed.rawRoom,?_⟩
  intro a
  have equal : tapeCells a 0 cs=tapeCells a 0 ds :=
    (redecode a (fun _ => false) cs 0 0).symm.trans
      ((congrArg (tapeCells a 0) clear).trans (redecode a (fun _ => false) ds 0 0))
  exact equal ▸ seed.inputs a

/-- The sampled tail changes neither the immutable headers nor the occupied
site's delivered operand words and bounds. This also holds on failed proposals. -/
theorem SameReportCells.source_received (m₀ : ℕ → ℕ)
    (held : ∀ c∈cs, c.Received w description m₀) (source : ReportAssignments ds) :
    ∀ c∈source.val, c.Received w description m₀ := by
  obtain ⟨layout,clear⟩ := same
  subst k
  change eraseReportBits cs=eraseReportBits ds at clear
  let z : ReportAssignments cs := ⟨source.val,source.property.trans clear.symm⟩
  let tape := (reportAssignmentEquiv cs).symm z
  have eqn : cellsOfTape cs tape=source.val := congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply z)
  intro c h
  rw [←eqn] at h
  obtain ⟨d,hd,offset,rfl⟩ := from_cells _ cs 0 h
  exact tape_Received (held d hd) _ offset

variable (seed : PreparedReportInput pub m cs q description) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (src : ReportAssignments ds)

/-- The inverse report assignment on the physical rows returns exactly the
same trace and memory as running the source row assignment on that control
state. The bit equality is obtained from the program's choice stream. -/
theorem SameReportCells.source_return :
    assignedReportReturnEquiv seed mac s (same.equiv.symm src) =
      assignedReportReturnEquiv (same.source_seed seed) mac s src := by
  apply (reportReturnEquiv (same.source_seed seed) mac s).symm.injective
  apply List.ofFn_injective
  rw [←reportReturnEquiv_recover,←reportReturnEquiv_recover]
  have bits := same.equiv_bits (same.equiv.symm src)
  rw [Equiv.apply_symm_apply] at bits
  exact ((assignedReportReturnEquiv_spec seed mac s (same.equiv.symm src)).1.2.1.trans bits.symm).trans
    (assignedReportReturnEquiv_spec (same.source_seed seed) mac s src).1.2.1.symm

/-- On this actual report return the ledger's source tape is the exact
private report tape read by the machine, including unused or false bits. -/
theorem SameReportCells.returned_source_tape {z : Returns prepareCellReports pub mac s m}
    (ret : z=assignedReportReturnEquiv seed mac s (same.equiv.symm src)) :
    (reportReturnEquiv (same.source_seed seed) mac s).symm z=(reportAssignmentEquiv ds).symm src := by
  rw [ret,same.source_return seed mac s src]
  exact Equiv.symm_apply_apply _ _

/-- The ledger's cell list on that real native visit is exactly the source
proposal. This identifies the addresses, count bits, selections and order
together. -/
theorem SameReportCells.returned_source_rows {z : Returns prepareCellReports pub mac s m}
    (ret : z=assignedReportReturnEquiv seed mac s (same.equiv.symm src)) :
    cellsOfTape ds ((reportReturnEquiv (same.source_seed seed) mac s).symm z)=src.val := by
  rw [same.returned_source_tape seed mac s src ret]
  exact congrArg Subtype.val ((reportAssignmentEquiv ds).apply_symm_apply src)

/-- The binding records, supplemental counters and physical tail bits read
from the report output have the source candidate's exact contents. -/
theorem SameReportCells.returned_source_bindings (alloc : ReportAllocation pre post banks l cs q)
    {z : Returns prepareCellReports pub mac s m} (ret : z=assignedReportReturnEquiv seed mac s (same.equiv.symm src))
    (i : Fin src.val.length) :
    let previous := (src.val.take i.val).foldl (fun a c => c.after a) q
    src.val[i.val].BindingReadback previous (readings z.val.2.2) := by
  rw [ret,same.source_return seed mac s src]
  exact assignedReportReturn_bindingReadback (same.source_allocation alloc) (same.source_seed seed) mac s src i

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
