import OAI.Hierarchy.TraceReceiverRootPrice
import OAI.Hierarchy.TraceReceiverVisitTariff

namespace OAI
/-! # Joint native bill specialized to the actual physical stage clock -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat Diagonal PhysicalStage RAM
open TraceDistribution

theorem joint_root {F : Type} [Fintype F] [Field F] (B : Block F)
    {w levels ended stages depth degree k : ℕ} (T : Diagonal.HistoryContraction.Tree F k)
    (charge ports rootCost : ℕ) (large : max 64 B.stageClockRate≤w) (count : levels≤w)
    (endCount : ended≤ stages) (height : depth≤ stages+4)
    (within : Diagonal.HistoryContraction.Tree.Within depth T) (coeff : 0<B.localCoefficient)
    (positive : 0<charge) (localPins : ports≤2*charge)
    (resources : T.resources≤Run.treeFee (B.localCoefficient*(64*w+1)^3) stages*charge)
    (terminal : rootCost≤TickTerminalRoot.rootFactor*
      (degree+4*Run.treeFee (B.localCoefficient*(64*w+1)^3) stages+3)*charge) :
    let fee:=B.nativeVisitFee levels (B.localCoefficient*(64*w+1)^3) ended
    let setup:=setupPrice stages B.stageClockRate
    fee*charge+(T.replayWork setup+
      (7224+19+1016*T.compile.cells+(9+5*T.compile.internal+22*T.compile.cells))+rootCost)+
        (perRoot+22*ports) ≤
      FactorWork.archiveTariff w depth (setupPrice stages (fullRate B.stageClockRate 0))
        (mapPrice degree TickTerminalRoot.rootFactor) stages B.localCoefficient*charge :=
  joint_root_rate B.stageClockRate B.localCoefficient T charge ports rootCost large count endCount height
    within coeff positive localPins resources terminal

end Hierarchy.TraceFactorReceiver.Gather
end

end OAI
