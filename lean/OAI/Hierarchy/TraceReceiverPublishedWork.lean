import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows
import OAI.Computability.VPVNP.RAMExecution

namespace OAI
/-! # The work column at a terminal physical site and its exact sum -/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open scoped Classical BigOperators
variable {F : Type} [Field F]

/-- The allowance read from the terminal site's first archive charge column. -/
def publishedWork {d lanes : ℕ} {A : State d lanes} (R : Run F A)
    (h : R.plan.History) (C : R.Charges) (start : A.Site → ℕ) (unitWork : ℕ)
    (v : (R.plan.finish h).Site) :=
  unitWork*R.chargeAt h C start v

theorem publishedWork_sum {d lanes : ℕ} {A : State d lanes} (R : Run F A)
    (h : R.plan.History) (C : R.Charges) (start : A.Site → ℕ) (unitWork : ℕ) :
    (∑ v, publishedWork R h C start unitWork v) = unitWork*R.rootTotal h C start := by
  simp only [publishedWork, ← Finset.mul_sum, R.chargeAt_sum]

variable {d lanes : ℕ} {A : State d lanes}
variable (r : Run F A) (h : r.plan.History) (C : r.Charges) (start : A.Site → ℕ)

/-- The data word at a terminal site's first S43 column equals the exact
work allowance used by the native-factor and paper-scale bounds. -/
theorem archived_work_eq {w : ℕ} (b : RAM.NavigationNodeRows.Banks) (m : Computability.VPVNP.BurstRAM.Memory w)
    (O : A.ArchiveSites) (path : r.ArchivePath h C O) (pairs : A.Site → ℕ)
    (stored : r.ArchiveRowsStored b (fun i => (m i).val) h C O path)
    (seed : O.Charged b (fun i => (m i).val) start pairs) (v : (r.plan.finish h).Site) :
    let last := r.finalArchive h C O path
    let row := last.1.first+(last.2 ((r.finalSite h).symm v)).val
    (m (b.charges+2*row)).val = publishedWork r h C start b.unitWork v := by
  have eqn := (r.archive_charges h C O path b (fun i => (m i).val) stored start pairs seed v).1
  simpa only [archiveColumn, Fin.val_zero, Nat.add_zero, publishedWork] using eqn

theorem archived_work_fits {w : ℕ} (b : RAM.NavigationNodeRows.Banks) (m : Computability.VPVNP.BurstRAM.Memory w)
    (O : A.ArchiveSites) (path : r.ArchivePath h C O) (pairs : A.Site → ℕ)
    (stored : r.ArchiveRowsStored b (fun i => (m i).val) h C O path)
    (seed : O.Charged b (fun i => (m i).val) start pairs) (v : (r.plan.finish h).Site) :
    publishedWork r h C start b.unitWork v < 2^w := by
  rw [← archived_work_eq r h C start b m O path pairs stored seed v]
  exact (m _).isLt

end Hierarchy.TraceDistribution.Physical
end

end OAI
