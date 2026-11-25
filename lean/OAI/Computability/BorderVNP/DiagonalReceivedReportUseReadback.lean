import OAI.Computability.BorderVNP.DiagonalReturnedReportBundles
import OAI.Computability.BorderVNP.CubePhysicalReceivedLedgerOrder
import OAI.Computability.BorderVNP.DiagonalNativeReportBindings

/-! # The checked source bundles on the actual all-team report tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open DiagonalTallyCellReports Packing.BottomReports Packing.BundleDirectory CellSparse
open private tapeCells_get from OAI.Computability.BorderVNP.DiagonalNativeReportBindings

variable {T C n w : ℕ} {l : ReportLayout} (R : ReceivedRows (fun _ : Fin T => l) C)
    (tape : Fin T → ℕ → Bool) (start : Fin T → ℕ)

/-- The count and use stream at a published global ordinal begins after every
earlier cell of its team. The same formula applies to each proposed report tape. -/
theorem reportedWithTape_at (t : Fin T) (i : Fin (R.cells t).length) :
    R.reportedWithTape tape start (R.order ⟨t,i⟩) =
      ((R.cells t).get i).withTape (tape t) (start t+(((R.cells t).take i.val).map ReportCell.tailWidth).sum) := by
  let get (j : (t : Fin T) × Fin (R.cells t).length) := (tapeCells (tape j.1) (start j.1) (R.cells j.1)).get
    (Fin.cast (tapeCells_length ..).symm j.2)
  exact (congrArg get (R.order.symm_apply_apply ⟨t,i⟩)).trans (tapeCells_get (tape t) (start t) (R.cells t) i)

variable (assigned : ((t : Fin T) × Fin (R.cells t).length) → AssignedCell l)
    (same : ∀ j,(assigned j).report=(R.cells j.1).get j.2)
    (passes : ∀ j,(assigned j).Passing w n)
    (returns : ∀ j, ∃ ret, (assigned j).Returns w n (R.reportedWithTape tape start (R.order j)) ret)
    {J : ℕ} (host : Fin J → Fin C) (bundles : Fin J → Bundle) (body : Fin J → List Factor)
    (before : Fin J → ℕ → Bool)
    (placed : ∀ j, (assigned j).bundles=(sourceRows host (R.order j).val).map bundles)
    (published : ∀ j,(assigned j).report.bundles=(sourceRows host (R.order j).val).map fun t =>
        physicalBundle (bundles t).header (body t) (bundles t).factors (before t))

/-- The source's chosen private bank is the one of its actual final host. -/
def reportSourceBank (j : Fin J) : ℕ → Bool :=
  lookup (assigned (R.order.symm (host j))).pre

include same passes returns placed published in
/-- Every returned native report lists exactly the source bundles of its
global cell, in their stable order and with flags read from the actual private
assignments. In particular the result is independent of the initial placeholder
values in the immutable source directory. -/
theorem reportedWithTape_bundles (c : Fin C) :
    (R.reportedWithTape tape start c).bundles = (sourceRows host c.val).map fun t =>
      physicalBundle (bundles t).header (body t) (bundles t).factors (R.reportSourceBank assigned host t) := by
  obtain ⟨j,rfl⟩ := R.order.surjective c
  let offset := start j.1+(((R.cells j.1).take j.2.val).map ReportCell.tailWidth).sum
  have row : R.reportedWithTape tape start (R.order j)=(assigned j).report.withTape (tape j.1) offset := by
    rw [same]
    exact R.reportedWithTape_at tape start j.1 j.2
  obtain ⟨ret,run⟩ := returns j
  rw [row] at run ⊢
  have phys := (assigned j).returned_bundles (passes j) (sourceRows host (R.order j).val)
    bundles body before (placed j) (published j) (tape j.1) offset ret run
  refine phys.trans (List.map_congr_left fun t ht => ?_)
  have owner : host t=R.order j := Fin.ext (mem_sourceRows.mp ht)
  simp only [reportSourceBank,owner,Equiv.symm_apply_apply]

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
