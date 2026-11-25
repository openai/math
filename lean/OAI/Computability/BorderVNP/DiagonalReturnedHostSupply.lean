import OAI.Computability.BorderVNP.DiagonalReportSupplyPreserved
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenReadback
import OAI.Computability.BorderVNP.CubeHostScatterPhysicalReadback
import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling

/-! # The scattered endpoint and free-literal words after the signed report scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube DiagonalTallyCellReports DiagonalTallyAllocation
open FiniteEvaluator CompactMachine

/-- The public controls and the actual report scanner after an owned return. The
returned report may serve a fit proof before its sparse argument writer is run. -/
structure ReportsThrough {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) where
  /-- The host copies and public cell controls start at the returning owned registers and memory. -/
  controls : Returns SignedPrep.controls pub mac s m
  /-- The cell report scanner starts from that actual control return. -/
  reports : Returns prepareCellReports pub mac controls.val.2.1 controls.val.2.2

variable {w description : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    (V : ReportsThrough pub mac s m) {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}

/-- Every supplied source word remains exactly the one copied by the
host from its selected packet or singleton. This compares the actual
intermediate host image with the actual memory after both later blocks. -/
theorem ReportsThrough.report_host_word (a : CubeArena.Layout) (H : OpenSuffix.Inputs)
    (ready : OpenSuffix.Ready H (pub 0).val (readings m) w)
    (placed : OpenSuffix.Placement H a pre (pub 0).val (readings m))
    (alloc : ReportAllocation pre post banks l cs q)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (i : Fin cs.length) (j : Fin cs[i.val].supplied) :
    readings V.reports.val.2.2 (cs[i.val].external+j.val) =
      OpenSuffix.hostImage (pub 0).val (readings m) (cs[i.val].external+j.val) := by
  rw [returned_report_supply alloc seed V.reports i j]
  have member : cs[i.val]∈cs := List.getElem_mem _
  have low := (alloc.banksOrdered cs[i.val] member).1
  rw [alloc.widths] at low
  change cs[i.val].external+cs[i.val].supplied+cs[i.val].tailWidth≤pre.start at low
  have below : cs[i.val].external+j.val<pre.start := by have bound := j.isLt; omega
  have window : pre.start ≤ pre.four ∧ pre.start≤pre.six ∧ pre.start≤pre.ranges ∧ pre.start≤pre.bundleTable := by
    simp only [BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.six,BeforeTasks.four,
      BeforeTasks.merged,BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.tailWidths]
    omega
  apply HostScatter.read_host_after_controls H ready V.controls.property
  · exact Or.inl (below.trans_le (placed.ranges ▸ window.2.2.1))
  · exact Or.inl (below.trans_le (placed.bundles ▸ window.2.2.2))
  · rw [CellControlRows.Layout.outputs,placed.four,placed.six,ready.controlBase,seed.framePointer]
    have frame := alloc.frameBefore
    have bank := (alloc.receiving cs[i.val] member).1
    simp only [CellBanks.Layout.bank] at bank
    omega


/-- Discard the argument return from an already completed signed visit. -/
def Visits.throughReports {n b h copies symbols : ℕ} {id : TableEntry n b h copies symbols → ℕ}
    (V : Visits id pub mac s m) : ReportsThrough pub mac V.owned.val.2.1 V.owned.val.2.2 :=
  ⟨V.controls,V.reports⟩

variable {n b h copies symbols : ℕ} {id : TableEntry n b h copies symbols → ℕ}
    (visit : Visits id pub mac s m)

/-- Every supplied source word remains exactly the one copied by the
host from its selected packet or singleton. This compares the actual
intermediate host image with the actual memory after both later blocks. -/
theorem Visits.report_host_word (a : CubeArena.Layout) (H : OpenSuffix.Inputs)
    (ready : OpenSuffix.Ready H (pub 0).val (readings visit.owned.val.2.2) w)
    (placed : OpenSuffix.Placement H a pre (pub 0).val (readings visit.owned.val.2.2))
    (alloc : ReportAllocation pre post banks l cs q)
    (seed : PreparedReportInput pub visit.controls.val.2.2 cs q description)
    (i : Fin cs.length) (j : Fin cs[i.val].supplied) :
    readings visit.reports.val.2.2 (cs[i.val].external+j.val) =
      OpenSuffix.hostImage (pub 0).val (readings visit.owned.val.2.2) (cs[i.val].external+j.val) := by
  exact visit.throughReports.report_host_word a H ready placed alloc seed i j

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
