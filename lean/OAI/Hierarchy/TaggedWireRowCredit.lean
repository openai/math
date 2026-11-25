import OAI.Hierarchy.ProtocolRAMStockPortPlan
import OAI.Hierarchy.ProbeRepairHistogramAccount

namespace OAI
/-! # Integer width credited to each destination by the original elected histogram rows -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram AdaptiveProbe
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {q d rows w : ℕ} {s : StockCommit} {b : Batch q d} {m : Memory w}

/-- Sum of the true credited amounts on one original candidate, restricted to
the chosen destination. The test may inspect its old stock address or its
separate physical edge label, or both. -/
def PortPlan.rowCredit (L : PortPlan s b m rows) (j : Fin rows)
    (accept : Fin s.occurrences → Prop) : ℕ :=
  ∑ v : Fin d, if accept (L.enum ⟨j,v⟩) then installedBits s.columns m (L.enum ⟨j,v⟩) else 0

theorem PortPlan.rowCredit_off (L : PortPlan s b m rows) (j : Fin rows)
    (off : j ∉ liveRows b m rows) (accept : Fin s.occurrences → Prop) :
    L.rowCredit j accept=0 := by
  unfold rowCredit
  apply Finset.sum_eq_zero
  intro v _
  have quiet := (L.off (L.enum ⟨j,v⟩) (by simpa using off)).1
  simp [quiet]

theorem PortPlan.sum_rowCredit (L : PortPlan s b m rows) (accept : Fin s.occurrences → Prop) :
    (∑ j : Fin rows, L.rowCredit j accept)=
      ∑ e : Fin s.occurrences, if accept e then installedBits s.columns m e else 0 := by
  rw [← L.enum.sum_comp (fun e => if accept e then installedBits s.columns m e else 0),Fintype.sum_sigma]
  rfl

theorem PortPlan.stock_rowCredit (L : PortPlan s b m rows) (i : Fin s.goods) :
    (∑ j : Fin rows, L.rowCredit j (fun e => kind s.plan.bank s.columns m e=some i)) =
      OuterBank.resourceBits (E := Fin s.occurrences) (kind s.plan.bank s.columns m) (installedBits s.columns m) i := by
  refine (L.sum_rowCredit (fun e => kind s.plan.bank s.columns m e = some i)).trans ?_
  unfold OuterBank.resourceBits
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : kind s.plan.bank s.columns m e = some i <;> simp [h]

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
