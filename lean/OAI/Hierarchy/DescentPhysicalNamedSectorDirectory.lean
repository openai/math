import OAI.Hierarchy.DescentPhysicalResetDateOperands
import OAI.Hierarchy.DescentNamedResetAtlas
import OAI.Hierarchy.DescentPhysicalRankPortPhase

namespace OAI
/-! # Public sector order and compact port table of the named reset date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentWalshPrecision DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage DescentResetGates ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
    (io : Dated.Operands) (floor : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "mid" => (a).successor.middle
local notation "cc" => S.groupWidth k tail age
local notation "oldCap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "dep" => GroupStage.depthBound venue.degree n f g

local notation "v₀" => (a).successor
local notation "b₀" => (a).rebased ((a).stageStart floor)

def namedSectorDirectory : (a).SectorDirectory where
  stems := 2*(2^k*(2*oldCap))
  pageBits := Nat.clog 2 (v₀).sheets.rows
  count := rfl
  ports := (v₀).rankPorts b₀
  before := DescentResetLocalRoster.publicBefore venue.degree k n dep cc oldCap (DescentResetLocalRoster.programCount board dep)
  sourceSlot j := DescentResetLocalRoster.publicSourceSlot venue.degree k n dep oldCap (DescentResetLocalRoster.programCount board dep) (v₀).receiver.candidates j.val

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
