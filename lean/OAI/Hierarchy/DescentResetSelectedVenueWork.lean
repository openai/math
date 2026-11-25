import OAI.Hierarchy.DescentResetVenueCoefficient
import OAI.Hierarchy.DescentResetSelectedRootRooms

namespace OAI
namespace Hierarchy.DescentSixParty.NativePitch
open DescentDatedAddressBook DescentCompiler TerminalScale DescentPackedWalsh
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail i p f g drift degree h nextM C packet oldLanes primitiveLanes printedBits : ℕ)
    (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ)
local notation "prev" => resetCut S k tail p f h i
local notation "e" => PhysicalReset.receiverCut G S board k tail i p f g drift degree h prev nextM C packet oldLanes primitiveLanes printedBits old
local notation "date" => PhysicalReset.selected G S board k tail i p f g drift degree h prev nextM C packet oldLanes primitiveLanes
  printedBits old io.wire io.roster floor
local notation "v" => (date).successor
local notation "pr" => ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old
local notation "at₀" => (date).rebased ((date).stageStart floor)
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take i).prod*256

theorem selected_venue_work (D rate : ℕ) (live : i < S.length) (radix : S.radix=2^k)
    (origin : old.hosts=S.hostSize i) (size : old.k=k) (degreeAt : old.degree=D)
    (next : nextM ≤ h/2) (rootRoom : 8*(v).groupWidth ≤ h)
    (blocks : 2^k ≤ scale S.height rate) (previous : cap ≤ scale S.height rate)
    (grow : 2^S.hostGain*S.radix ≤ scale S.height rate) :
    (v).venue.fee ≤ ResetOutput.venueLead n d D f g*scale S.height (3*rate)*
      ResetOutput.venueArea h (S.hostSize i) (S.groupCount i) (S.groupCount (i+1)) (2^e) nextM := by
  let issued := ResetOutput.fromBoard G S board k tail i p f g drift degree h e prev (2^e) nextM C packet pr at₀
  have output : (v) = issued := PhysicalReset.named_successor G S board k tail i p f g drift degree h e prev
    (2^e) nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  have inventory := PhysicalReset.selected_inventory G S board k tail i p f g drift degree h prev nextM C
    packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  let seed := ResetOutput.fromBoard G S board k tail i p f g drift degree h 0 prev 1 nextM C packet pr 0
  have width : (v).groupWidth = seed.groupWidth := by
    have roots : (v).rootUnits = seed.rootUnits := inventory.1
    have receivers : (v).receiverUnits = seed.receiverUnits := inventory.2.1
    unfold ResetOutput.groupWidth
    rw [roots, receivers]
  have fits (x : ℕ) (used : x∈issued.rootUnits ∨ x∈issued.receiverUnits) : x*2^e ≤ h/2 := by
    rw [←output] at used
    have paid := PhysicalReset.selected_room G S board k tail i p f g drift degree h prev nextM C
      packet oldLanes primitiveLanes printedBits old io.wire io.roster floor x (width ▸ rootRoom) used
    rwa [inventory.2.2.1] at paid
  have total := ResetOutput.original_venue_bill G S board k tail i p f g drift degree h e prev nextM C packet pr at₀
    live radix origin next fits
  have factor:=ResetOutput.original_venue_coefficient G S board k tail i p f g drift degree h e prev nextM C packet pr at₀
    D S.height rate degreeAt size blocks previous grow
  rw [output]
  exact total.trans (Nat.mul_le_mul_right _ factor)

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
