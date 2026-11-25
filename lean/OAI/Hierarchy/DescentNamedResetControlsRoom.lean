import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentResetControlCuts
import OAI.Hierarchy.DescentNamedPriorVenueRoom

namespace OAI
/-! The receiver's control columns read the shape-major scene and the two banks
from the already measured actor census. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

local notation "U" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

theorem DateInputs.fromNamed_controls_room (previousMeta previousArguments : ℕ) (initial : Bool)
    (prepared : (rc).PreparedFits book) (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (homes : venue.hosts=S.hostSize age) (groups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (within : age<S.length) (lanes : 0<M) (top : (a).fullEnd floor<2^w) :
    (v).ControlRoom base₀ (U previousMeta previousArguments initial prepared scene).bank w := by
  let u := U previousMeta previousArguments initial prepared scene
  let R := (v).actor.directory actorBase
  obtain ⟨before,hostFit,startFit,stopFit⟩ := (v).control_address_bounds base₀
  have absolute : (v).metadataEnd base₀<2^w := top
  have later := ((v).cuts base₀).metadata.trans_lt absolute
  have ceiling := stopFit.trans_lt later
  have low := startFit.trans_lt ceiling
  have oldFit : R.endAddress<2^w := before.trans_lt low
  obtain ⟨_,_,_,census,inverse⟩ := R.fits oldFit
  have actorEnd : (v).actor.endAddress actorBase≤early := Nat.le_add_right ..
  have sceneFit : ((v).actor.scene actorBase).Fits w ((v).controlFloor base₀) := by
    have above : ((v).actor.scene actorBase).base+((v).actor.scene actorBase).size≤(v).controlFloor base₀ :=
      actorEnd.trans before
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (above.trans_lt low),above⟩
  have number : u.bank.count.Fits w ((v).controlFloor base₀) :=
    ⟨census.1,census.2.1,census.2.2.trans before⟩
  have inv : u.bank.inverse.Fits w ((v).controlFloor base₀) :=
    ⟨inverse.1,inverse.2.1,inverse.2.2.trans before⟩
  have splitGroups : S.groupCount (age+1)*2^k=2^cc := by
    rw [S.group_cut within,pow_add,S.group_power groups radix]
  apply (v).control_room base₀ u.bank sceneFit number inv
  · change (v).actor.shapes*(venue.hosts*chunks (S.groupCount (age+1)*2^k) (2^e))≤
      ((v).actor.scene actorBase).size
    rw [homes,splitGroups]
    exact (v).actor.extent_scene actorBase
  · change (v).sheets.hosts≤2^w
    exact hostFit.trans low.le
  · exact lanes
  · exact Nat.two_pow_pos _
  · exact ceiling

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
