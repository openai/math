import OAI.Hierarchy.TraceReceiverVisitArithmetic
import OAI.Hierarchy.TraceFactorWork
import OAI.ThreeFlat.Diagonal.PhysicalVisitRates
import OAI.ThreeFlat.Diagonal.PhysicalRefreshLocalPrices
import OAI.ThreeFlat.Diagonal.PhysicalTreeFee

namespace OAI
/-! # The assigned chronological stage clock fits the registered finite tariff -/

namespace Hierarchy.TraceReceiverRunCost
open ThreeFlat Diagonal PhysicalStage TraceDistribution Filter
open scoped Classical
variable {F : Type} [Fintype F] [Field F]

/-- The two charged portions are bounded jointly in the original S43 unit,
before multiplying by the actual inherited work at each terminal factor. -/
theorem joint_fee (B : Block F) {w levels ended stages : ℕ} (depth setup maps : ℕ)
    (large : max 64 B.stageClockRate ≤ w) (count : levels≤w) (endCount : ended≤ stages) :
    B.nativeVisitFee levels (B.localCoefficient*(64*w+1)^3) ended +
        (10025+1016*depth+setup+maps)*Run.treeFee (B.localCoefficient*(64*w+1)^3) stages ≤
      FactorWork.archiveTariff w depth setup maps stages B.localCoefficient :=
  TraceReceiverVisitArithmetic.joint_fee B.stageClockRate B.localCoefficient depth setup maps large count endCount

theorem fee_le_tariff (B : Block F) {w levels ended stages : ℕ} (depth setup maps : ℕ)
    (large : max 64 B.stageClockRate ≤ w) (count : levels≤w) (endCount : ended≤ stages) :
    B.nativeVisitFee levels (B.localCoefficient*(64*w+1)^3) ended ≤
      FactorWork.archiveTariff w depth setup maps stages B.localCoefficient :=
  (Nat.le_add_right ..).trans (joint_fee B depth setup maps large count endCount)

end Hierarchy.TraceReceiverRunCost

end OAI
