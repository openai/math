import OAI.Hierarchy.ProtocolRAMTurnChart
import OAI.Hierarchy.ProtocolRAMTurnInstalled

namespace OAI
/-! # Native code for the chronological gate shelf -/
noncomputable section
namespace Hierarchy.ProtocolRAMChronologicalShelf
open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM ProtocolRAMTurnItinerary ProtocolRAMTurnChart
def program (W N sites slots header bits initial src sb rom rb base scratch sink : ℕ)
    (d : Data) (heads : Bank) (b : Banks) :=
  (ProtocolRAMVisitColumns.program W N initial (walk header bits d b.edge b.tailSite heads)).seq
    (ProtocolRAMTurnInstalled.program W N sites slots src base scratch sink (chart header bits d) b
      (ProtocolRAMTurnShelf.tables rom rb src sb N))

end Hierarchy.ProtocolRAMChronologicalShelf
end

end OAI
