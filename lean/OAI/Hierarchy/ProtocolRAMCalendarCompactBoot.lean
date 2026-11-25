import OAI.Hierarchy.ProtocolRAMCalendarCompactRun
import OAI.Hierarchy.ProbeStageCompact

namespace OAI
/-! # Operations used by the counted calendar admission program -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.Boot
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical

theorem compact_program_cheap {h d q goods : ℕ} (C : Chart (wordBits h d copies) q goods) (flag : ℕ) :
    CheapCode (compactProgram C flag) := cheap_seq (Native.Compact.subdivision_cheap h d) (checked_cheap C flag)

end Hierarchy.ProtocolRAM.Calendar.Boot
end

end OAI
