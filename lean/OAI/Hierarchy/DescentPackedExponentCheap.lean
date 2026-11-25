import OAI.Hierarchy.DescentPackedExponentProgram
import OAI.Hierarchy.ProtocolRAMStaticSlotCheap
import OAI.Hierarchy.ProtocolRAMEndpointPrefixCheap

namespace OAI
namespace Hierarchy.DescentPackedTerminalExponent
open ProtocolRAM DescentPackedPrivateSum
variable (L : Layout) (O : DescentPrivateExponentRAM.Banks)
theorem cheap (w n M p : ℕ) : CheapCode (program L O w n M p) := by
  let rows := Layout.count 1 n M
  have counts : CheapCode (L.program w 1 n M) :=
    @cheap_seq w (scan w L.words rows (DescentPackedScore.read L.source L.rom))
      (ProtocolRAMEndpointPrefix.exclusive w L.words L.starts rows) (@scan_cheap w L.words rows (DescentPackedScore.read L.source L.rom))
      (@ProtocolRAMRankCheap.exclusive_cheap w L.words L.starts rows)
  have exponent : CheapCode (O.program w p) :=
    @cheap_seq w (ProtocolRAMStaticPorts.program w O.usedBits 1 p (DescentPrivateEdgeCounter.cell O.usedWords))
      (scan w O.deadBits 1 O.minus) (@ProtocolRAMStaticPortCheap.base w O.usedBits 1 p (DescentPrivateEdgeCounter.cell O.usedWords))
      (@scan_cheap w O.deadBits 1 O.minus)
  exact @cheap_seq w (L.program w 1 n M) (O.program w p) (@counts) (@exponent)

end Hierarchy.DescentPackedTerminalExponent

end OAI
