import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialCore
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialPackets
import OAI.Optimization.LinearProgramming.PriceGame.ControlFeedback

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

abbrev MachineState := State NodeInput Prepared PackedRound Completed
abbrev ReturnFrame := Frame NodeInput Prepared Completed

/-- All saved machine state is instantiated by finite lists or scalar counters. -/
def packetKernelSized (scan : FeedbackScan) (N R r ne : ℕ) (experts : List PackedExpert) :
    Kernel NodeInput Prepared PackedRound Completed PackedQuery where
  leaf := leafPacket N R ne
  prepare := preparePacketSized N r ne experts
  childInput := descend
  assemble := assemblePacketSized N r ne experts
  finish := completeSized scan N ne experts

def packetKernel (scan : FeedbackScan) (N R r : ℕ) (experts : List PackedExpert) :
    Kernel NodeInput Prepared PackedRound Completed PackedQuery :=
  packetKernelSized scan N R r experts.length experts

/-- The first-order machine with the concrete single-coordinate feedback implementation. -/
def stepPacket (N R r : ℕ) (experts : List PackedExpert) (s : MachineState) :
    Action NodeInput Prepared PackedRound Completed PackedQuery :=
  step (packetKernel feedbackPrefix N R r experts) (2*r) s

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
