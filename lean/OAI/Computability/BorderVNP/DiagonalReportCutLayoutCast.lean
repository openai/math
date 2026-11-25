import OAI.Computability.BorderVNP.DiagonalReceivedReportLayoutCast
import OAI.Computability.BorderVNP.DiagonalSourceReturnedInputs

/-! # Restoring original report assignments at the actual processor frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open VPVNP.BurstRAM DiagonalTallyCellReports DiagonalTallyAllocation RoutingISA
open RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep

variable {T C : ℕ} {l l' : ReportLayout} (R : ReceivedRows (fun _ : Fin T => l) C)

/-- Carry the same finite assignment at every physical cell across the
equality identifying the common chart and the installed processor frame. -/
def assignmentsAtLayout (h : l=l') (src : ∀ u, ReportAssignments (R.cells u)) :
    ∀ u, ReportAssignments ((R.atLayout h).cells u) := by
  cases h
  exact src

/-- Encoding commutes with changing the chart by the actual frame equality. -/
theorem tapesAtLayout_assignments (h : l=l') (src : ∀ u, ReportAssignments (R.cells u)) :
    R.tapesAtLayout h (fun u => (reportAssignmentEquiv (R.cells u)).symm (src u)) =
      fun u => (reportAssignmentEquiv ((R.atLayout h).cells u)).symm (R.assignmentsAtLayout h src u) := by
  cases h
  rfl

/-- The same report scanner return has the same fitted sparse continuation
when reindexed to the actual physical frame. -/
def cutAtLayout (h : l=l') (src : ∀ u, ReportAssignments (R.cells u)) (t : Fin T)
    {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    (actual : Returns prepareCellReports pub mac s m) {cur : ReportCursor} {desc : ℕ}
    (cut : ReportArgumentCut actual (src t) cur desc) :
    ReportArgumentCut actual (R.assignmentsAtLayout h src t) cur desc := by
  cases h
  exact cut

/-- All installed addresses and capacity bounds belong to the same received
list after identifying the two physically equal report layouts. -/
theorem allocationAtLayout (h : l=l') (t : Fin T) {pre : BeforeTasks} {post : AfterTasks}
    {banks : CellBanks.Layout} {cur : ReportCursor}
    (alloc : ReportAllocation pre post banks l (R.cells t) cur) :
    ReportAllocation pre post banks l' ((R.atLayout h).cells t) cur := by
  cases h
  exact alloc

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
