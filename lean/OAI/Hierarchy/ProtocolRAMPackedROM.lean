import OAI.Hierarchy.ProtocolRAMPackedRanked
import OAI.Hierarchy.ProtocolRAMPackedBias

namespace OAI
/-! # Installed width-class and piece counters for the translated rank CPU -/

namespace Hierarchy.ProtocolRAMPackedRanked
open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM ProtocolRAMTranslatedKey ProtocolRAMReportedPorts TaggedShorterReportAdvice
open scoped Fin.CommRing

variable {W N w menu gb : ℕ}

theorem report_rom {groups D B M base cap rom bits : ℕ} (rows : Fin N→ProtocolRAMEmit.Row) (mem : Memory W)
    (pub : ∀j : Fin 13,∀x : ℕ,x < 2^bits→(bank rom bits j).read mem (x:Word W)=
      words groups D B M base w menu cap j x)
    (widthFit : ∀i,(rows i).width < 2^bits) :
    (∀i : Fin N,(bank rom bits 3).read mem ((rows i).width:Word W)=((classOf rows w menu i).val:Word W)) ∧
    (∀i : Fin N,(bank rom bits 4).read mem ((rows i).width:Word W)=(pieces rows w i:Word W)) :=
  ⟨fun i=>pub 3 _ (widthFit i),fun i=>pub 4 _ (widthFit i)⟩

end Hierarchy.ProtocolRAMPackedRanked

end OAI
