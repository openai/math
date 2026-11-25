import OAI.Hierarchy.TraceReceiverFullRate
import OAI.Hierarchy.TraceReceiverRootArithmetic
import OAI.ThreeFlat.RAM.TickTerminalRootPrice

namespace OAI
/-! # One original S43 resource word covers all native phases of a selected terminal -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat Diagonal RAM
open TraceDistribution

theorem joint_root_rate {F : Type} [Fintype F] [Field F] (rate coefficient : ℕ)
    {w levels ended stages depth degree k : ℕ} (T : Diagonal.HistoryContraction.Tree F k)
    (charge ports rootCost : ℕ) (large : max 64 rate≤w) (count : levels≤w)
    (endCount : ended≤ stages) (height : depth≤ stages+4)
    (within : Diagonal.HistoryContraction.Tree.Within depth T) (coeff : 0<coefficient)
    (positive : 0<charge) (localPins : ports≤2*charge)
    (resources : T.resources≤((2*stages+1)*(coefficient*(64*w+1)^3))*charge)
    (terminal : rootCost≤TickTerminalRoot.rootFactor*
      (degree+4*((2*stages+1)*(coefficient*(64*w+1)^3))+3)*charge) :
    let fee:=(ended+1)*(rate*(coefficient*(64*w+1)^3)*(4*levels+4))
    let setup:=setupPrice stages rate
    fee*charge+(T.replayWork setup+
      (7224+19+1016*T.compile.cells+(9+5*T.compile.internal+22*T.compile.cells))+rootCost)+
        (perRoot+22*ports) ≤
      FactorWork.archiveTariff w depth (setupPrice stages (fullRate rate 0))
        (mapPrice degree TickTerminalRoot.rootFactor) stages coefficient*charge :=
  joint_root_price rate coefficient TickTerminalRoot.rootFactor perRoot T charge ports rootCost
    large count endCount height within coeff positive localPins resources terminal

end Hierarchy.TraceFactorReceiver.Gather
end

end OAI
