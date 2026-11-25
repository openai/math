import OAI.Hierarchy.NativeFactorOrdinalCore
import OAI.Hierarchy.GridFactorPinSchedule

namespace OAI
/-! # Numbered input pins for the authentic physical trace -/

namespace Hierarchy.TraceDistribution.Physical
open ThreeFlat LinearAlgebra.SpectralBooks
open Diagonal Diagonal.HistoryContraction Diagonal.LaneCursor
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory
open FactorPinIntervals
open scoped BigOperators Classical
noncomputable section

variable {F : Type} [Field F] [Fintype F] {k low w pc regs words S base fuel N : ℕ}
    (B : PhysicalStage.Block F) (hk : 2≤k+1)
    (M : Machine w pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^w) (st : Word w) (s : ℕ) (fits : B.blockCharge*s≤k+1)

variable (h : (physicalPlan B hk M t hF st s fits).History) (archive : ((physicalPlan B hk M t hF st s fits).finish h).Site ≃ Fin N)

def ordinalScheduledPins {E : Type} {g n q d m : ℕ}
    (ht : 0<(n+1)^g*q) (scale : ℕ) (cost : Fin N→Fin m→ℕ)
    (header : GridThrough.Cell g n × Fin q→List Bool) (advice : Fin S→Bool)
    (room : ∀ tt : GridThrough.Cell g n × Fin q, (header tt).length +
      ((FactorAllocation.factors scale cost (List.finRange N) (GridTicks.index tt)).map
        (fun i => (Finset.univ.filter (fun j => origin B hk M t hF st s fits h archive j=i)).card)).sum ≤ d)
    (rail : E ↪ Fin (S/2)) (direction : E→Fin g) : GridThrough.PinAssignment E g n q d :=
  scheduledPins ht scale cost (origin B hk M t hF st s fits h archive) header advice room rail direction
    (origin_pair B hk M t hF st s fits h archive)

end
end Hierarchy.TraceDistribution.Physical

end OAI
