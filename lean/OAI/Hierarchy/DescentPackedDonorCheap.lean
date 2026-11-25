import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentPackedDonorTables
import OAI.Hierarchy.DescentPackedPrivateAccumulatorCheap

namespace OAI
/-! # The fixed donor table setup and its complete account use only cheap instructions -/
namespace Hierarchy
open ProtocolRAM DescentSIMDLookup

namespace DescentPackedDonorTables

theorem stage_cheap (bank : Banks) (L : DescentPackedPrivateSum.Layout) (C : DescentPackedPrivateAccumulator.Counters)
    (H J M w grain : ℕ) {a b : ℕ} (resolver : Cell a→Cell (b*11)) (score : Cell b→ℕ) :
    CheapCode ((program bank L.rom.base H J M w resolver score).seq
      ((DescentSIMDLookup.program bank L.source.base H J M w).seq
        (DescentPackedPrivateAccumulator.program L C w H (J*11) (M*11) grain))) :=
  @cheap_seq w (program bank L.rom.base H J M w resolver score)
    ((DescentSIMDLookup.program bank L.source.base H J M w).seq
      (DescentPackedPrivateAccumulator.program L C w H (J*11) (M*11) grain))
    (@DescentStaticWordColumn.cheap w bank.mask.base (literal bank L.rom.base H J M resolver score)
      (size bank L.rom.base b M))
    (@cheap_seq w (DescentSIMDLookup.program bank L.source.base H J M w)
      (DescentPackedPrivateAccumulator.program L C w H (J*11) (M*11) grain)
      (@scan_cheap w L.source.base (H*chunks J M) (lookup bank))
      (@DescentPackedPrivateAccumulator.cheap L C w H (J*11) (M*11) grain))

end DescentPackedDonorTables
end Hierarchy

end OAI
