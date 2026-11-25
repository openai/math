import OAI.Hierarchy.ProtocolRAMStripColumnPrograms
import OAI.Hierarchy.ProtocolRAMBoughtPositionColumn

namespace OAI
/-! # Reading an internal tile of a previously purchased path at its fixed birth -/

noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets PurchaseFrozen
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {attempts : ℕ}

theorem Directory.atPosition_event (v : Directory attempts) (base : ℕ) (S : PurchaseSampler)
    (h W k depth K G H : ℕ) (j : Fin (depth+1)) (side : Bool) {w : ℕ} (m : Memory w)
    (a : Fin attempts) (r : Fin (v.header h (2^W) k S.degree depth).ports)
    (load : (v.header h (2^W) k S.degree depth).Loaded m) (room : attempts≤2^w) :
    (v.atPosition base S h W k depth K G H j side).eval m
      (((v.header h (2^W) k S.degree depth).enum ⟨a,r⟩).val:Word w)=
      (v.eventPosition (v.shelf a) base S h W k depth K G H j side).eval m (r.val:Word w) :=
  v.dispatch h (2^W) k S.degree depth m load room a r
    (fun e=>v.eventPosition (v.shelf e) base S h W k depth K G H j side)

end Hierarchy.ProtocolRAM.BoughtSockets
end

end OAI
