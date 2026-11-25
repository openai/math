import OAI.Hierarchy.ProbePayloadWords
import OAI.Hierarchy.ProbeStripReplayWords
import OAI.Hierarchy.ProtocolRAMVectorROMTable
import OAI.Hierarchy.ProtocolRAMCalendarDeadlineROM

namespace OAI
/-! # Immutable finite quote-vector tables for the two actual discrepancy tests

Both fixed-format tables coexist above the scalar-price pages. Only the
ordinals, public phase parameters, precision and finite field enter these words. -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DiscrepancyROM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage StripDirectory
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {w p D : ℕ}

def payload (F : Type*) [Field F] (N k : ℕ) [SiteNaming (PayloadStrip.Site N k)]
    (base radix precision : ℕ) (phase : Fin p→PhasePrice) : Table p (Fintype.card (PayloadStrip.Quotes N k)) :=
  ⟨base,radix,fun u=>payloadDiscrepancyCode F (phase u) precision radix⟩

def purchase (F : Type*) [Field F] (depth k : ℕ) [SiteNaming (ChainStrip.Site depth k)]
    (base radix precision : ℕ) (phase : Fin p→PhasePrice) : Table p (Fintype.card (ChainStrip.Axes depth k)) :=
  ⟨base,radix,fun u=>discrepancyCode F (phase u) (phase u).M precision radix⟩

end Hierarchy.ProtocolRAM.Calendar.DiscrepancyROM
end

end OAI
