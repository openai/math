import OAI.Computability.BorderVNP.DiagonalSameReportVisits
import OAI.Computability.BorderVNP.DiagonalSignedNativePacketSeeds
import OAI.Computability.BorderVNP.DiagonalReturnedReportSplice

/-! # The issued supplemental array is unchanged by the native report assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open DiagonalTallyCellReports DiagonalTallyAllocation
open scoped Classical

/-- A physical source and its selected report assignment have the same
supplemental bindings at every global address, including unowned cells.
Each owned key uses the unique compact index given by the true allocation. -/
theorem SameReportCells.seedExtras_eq {l k : ReportLayout} {cs : List (ReportCell l)} {ds : List (ReportCell k)}
    (same : SameReportCells cs ds) {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout} {q : ReportCursor}
    (allocated : ReportAllocation pre post banks l cs q) :
    seedExtras cs q=seedExtras ds q := by
  classical
  have saved := same.source_allocation allocated
  obtain ⟨layout,clear⟩ := same
  subst k
  let proposed : ReportAssignments cs := ⟨ds,clear.symm⟩
  let ix (i : Fin cs.length) : Fin ds.length := Fin.cast proposed.length.symm i
  have num (i : Fin cs.length) : ds[ix i].number=cs[i].number := by
    have raw := congrArg ReportCell.number (proposed.row_eq i)
    exact raw
  funext c
  by_cases h : ∃ i : Fin cs.length, cs[i].number=c
  · obtain ⟨i,hi⟩ := h
    rw [←hi,allocated.seedExtras_owned i,←num i,saved.seedExtras_owned (ix i)]
    change _ = bindingRows ds[ix i].bundles (ds[ix i].localStart ((proposed.val.take i.val).foldl (fun cur r => r.after cur) q))
    rw [proposed.take_cursor i.val q]
    exact (assigned_bindingRows proposed i _).symm
  · have missing : ¬∃ j : Fin ds.length, ds[j].number=c := by
      rintro ⟨j,hit⟩
      let i := Fin.cast proposed.length j
      exact h ⟨i,(num i).symm.trans hit⟩
    simp only [seedExtras,dite_eq_right h,dite_eq_right missing]

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
