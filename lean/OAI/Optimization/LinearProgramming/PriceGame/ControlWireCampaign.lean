import OAI.Optimization.LinearProgramming.PriceGame.ControlWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaign

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open ExactQuantumFactoring.BitStackProgram

def campaignStateCode (s : CampaignState) : List Bool :=
  prodCode packedPopulationCode (prodCode (listCode packedProbeCode) Nat.bits)
    (s.population,s.seen,s.positiveVotes)

def campaignCursorCode (c : CampaignCursor) : List Bool :=
  prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits
    (prodCode Nat.bits campaignStateCode)))) (c.dimension,c.range,c.anchor,c.total,c.left,c.state)

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
