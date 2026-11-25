import OAI.Hierarchy.DescentPackedPrivateAccumulator
import OAI.Hierarchy.ProtocolRAMEndpointPrefixCheap
import OAI.Hierarchy.ProtocolRAMStaticSlotCheap

namespace OAI
namespace Hierarchy.DescentPackedPrivateAccumulator
open ProtocolRAM DescentPackedPrivateSum DescentPrivateEdgeCounter

private theorem lookupCheap (L : Layout) (w H r M : ℕ) : CheapCode (L.program w H r M) :=
  @cheap_seq w
    (scan w L.words (Layout.count H r M) (DescentPackedScore.read L.source L.rom))
    (ProtocolRAMEndpointPrefix.exclusive w L.words L.starts (Layout.count H r M))
    (scan_cheap w L.words (Layout.count H r M) (DescentPackedScore.read L.source L.rom))
    (ProtocolRAMRankCheap.exclusive_cheap w L.words L.starts (Layout.count H r M))

private theorem additionCheap (C : Counters) (w grain : ℕ) : CheapCode (C.add w grain) :=
  @cheap_seq w (ProtocolRAMStaticPorts.program w C.scaled 1 grain (cell C.words))
    (scan w C.out 1 C.plus) (ProtocolRAMStaticPortCheap.base w C.scaled 1 grain (cell C.words))
    (scan_cheap w C.out 1 C.plus)

theorem cheap (L : Layout) (C : Counters) (w H r M grain : ℕ) :
    CheapCode (program L C w H r M grain) := by
  rw [program]
  exact @cheap_seq w (L.program w H r M) (C.add w grain) (@lookupCheap L w H r M) (@additionCheap C w grain)

end Hierarchy.DescentPackedPrivateAccumulator

end OAI
