import OAI.Hierarchy.ProbeStripPortBoard
import OAI.Hierarchy.ProtocolRAMCalendarLiveFormats

namespace OAI
/-! # Actual port-padded formats at the resolved chronological stock addresses -/

namespace Hierarchy.ProtocolRAM.PortPadding
open Computability.VPVNP.BurstRAM PrivateRAM
open PurchaseStage Calendar
open scoped Classical
noncomputable section
variable {w z d k q n p r D : ℕ}

def portfolio (c : Mesh) (a : Arena) (initial : ℕ) (shape : Attempt → Geometry z d k q p r)
    (start : Attempt → ℕ) (x : Attempt) : Format z d k q (max p r) :=
  liveFormats c a initial (fun t addr => (shape t).build (start t) addr) x

end
end Hierarchy.ProtocolRAM.PortPadding

end OAI
