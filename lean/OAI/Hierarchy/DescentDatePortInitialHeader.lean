import OAI.Hierarchy.DescentSeedRegisterPorts
import OAI.Hierarchy.DescentDatePortHeaderRoom
import OAI.Hierarchy.DescentSeedSharedCountBank

namespace OAI
/-! # The original host count, hub bits and numbered roster fit the first date's actual header -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedSeedStartup DescentSeedInitialTable Catalyst ProtocolRAM
noncomputable section
variable {F : Type} [Field F] {c p : ℕ} (G : PoweredGadget F) (op : RotorSpec)
  (X : Approximation F c p) (R : ℕ) (l : Layout) (k H groups payload Z : ℕ)
local notation "db" => directoryBase X l H groups k
local notation "top" => DescentDatedSeedStartup.endAddress X l H groups k
local notation "ports" => initial G op X R l k H groups payload Z
local notation "M" => l.packedLanes

theorem initial_header_room {w roof : ℕ} (order : top ≤ roof) (space : roof < 2^w) :
    (ports).HeaderRoom w roof :=by
  apply HeaderRoom.mono (floor:=top) _ order
  have under : DescentSeedInitialTable.endAddress db H groups M 3 < 2^w:=order.trans_lt space
  have cap:=capacities H groups M 3
  exact ⟨shared_host_fits db H groups M w under,
    bank_fits (c:=0) (by decide : 0<3+8) under,cap.2.1,
    bank_fits (c:=4) (by decide : 4<3+8) under,cap.1⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
