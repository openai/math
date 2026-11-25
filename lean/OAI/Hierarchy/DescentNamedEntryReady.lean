import OAI.Hierarchy.DescentNamedPrimeRoom
import OAI.Hierarchy.DescentNamedStencilRoom
import OAI.Hierarchy.DescentStencilOperandGeometry
import OAI.Hierarchy.DescentNamedStencilPacking
import OAI.Hierarchy.DescentNamedPreparedRootRoom
import OAI.Hierarchy.DescentNamedSceneStemRoom
import OAI.Hierarchy.DescentNamedActorReady

namespace OAI
/-! Published machine bounds through the actor directory on an original fixed reset date. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup DescentWalshPrecision
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open DescentColonies DescentPlainTerminal.Suffix DescentSixParty.PackedFlow.Padded ProtocolRAM
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
variable (fitsStencil : e ≤ laneBits (S.groupWidth k tail age + k) payload
    (S.localWalshBits p (S.groupWidth k tail age + k) f (quota S.rounds)) - k)
  (fitsSigned : e ≤ previous) (fitsCut : previous ≤ S.groupWidth k tail age) (count : Bank)
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
local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

local notation "front" => (v).front
local notation "bb" => S.localWalshBits p (cc+k) f (quota S.rounds)
local notation "prime₀" => (a).PrimeRoom start ((a).ingress.source floor) count (S.groupCount age) venue.degree w

/-- The actual layout requirements before the first issued branch. Each field concerns
a numerical rate, an address of the previous venue, or a true row capacity. -/
structure NamedEntrySpace : Prop where
  groups : S.baseGroups=2^tail
  radix : S.radix=2^k
  low : k≤wide
  pitch : M=2^e
  lookup : 8*bb≤payload
  word : payload≤w
  degree : venue.degree+1<2^w
  smooth : DescentBaseProfile.decayExponent venue.degree<2^w
  count : count.base+count.size≤floor
  roster : io.roster.base+io.roster.size≤floor
  rosterRows : S.hostSize age*venue.degree≤ io.roster.size
  hubs : io.hubs.Fits w floor
  hubRows : S.hostSize age≤ io.hubs.size
  wires : ∀(x:Block k)(j:Fin (2*cap)),(io.wire x.val j.val).Fits w floor ∧
    S.hostSize age*chunks (S.groupCount age) (2^previous)≤(io.wire x.val j.val).size
  exponent : e≤S.endpointExponent k tail age p f venue.degree payload n
  stencilWidths : 4*sharedWidth (S.endpointBook k tail age p f venue.degree payload n)≤payload
  selected : ∀t∈(v).rootUnits,t*(v).receiver.lanes≤payload/2
  markers : 2^e*max ((ResetMiddle.fieldWidth venue.degree cap n k Ht)*8) (front).peer.bits≤w/2
  ceiling : (a).fullEnd floor<2^w

include fitsStencil fitsSigned fitsCut

theorem named_entry_ready
    (space : NamedEntrySpace G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w count) :
    prime₀ ∧ (P).Room w ∧ (rc).PreparedFits book ∧
      (front).SceneRoom ((v).actorEnd base₀) ((v).issuedScene base₀ older) w := by
  have prime:=named_prime_room G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor count w (S.group_power space.groups space.radix age) space.low
    space.lookup space.word space.smooth space.count space.roster space.rosterRows space.ceiling
  have cut:=named_chip_cut G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor
  have operands:=(a).stencil_operand_geometry sh floor count io.hubs g (2^n) w prime space.hubs rfl space.ceiling
  obtain ⟨short,word⟩:=named_stencil_packing G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor count w sh space.exponent space.stencilWidths space.word
  have stencil:=(a).stencil_room_of_end sh floor count io.hubs g (2^n) w cut space.ceiling operands short word
  obtain ⟨prepared,sender⟩:=named_prepared_and_sender G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count space.pitch space.groups space.radix
    space.wires space.selected space.word space.ceiling stencil prime.fit
  have laid : (rc).preparedEnd book≤(v).actorEnd base₀:=by
    rw [named_root_prepared_end G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count]
    exact ((v).cuts base₀).actors
  have pos:0<M:=by rw [space.pitch]; exact Nat.two_pow_pos e
  have isSmall : 4<2^w:=by
    have h:0<bb:=(a).positive
    have h₁:=space.lookup
    have h₂:=space.word
    have h₃:=Nat.lt_two_pow_self (n:=w)
    omega
  have hosts:S.hostSize age<2^w:=
    space.hubRows.trans_lt space.hubs.2.1
  have scene:=named_scene_ready G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count pos
    stencil sender laid isSmall hosts space.degree space.markers space.hubs space.ceiling
  exact ⟨prime,stencil,prepared,scene⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
