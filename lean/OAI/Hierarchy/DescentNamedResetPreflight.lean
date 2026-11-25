import OAI.Hierarchy.DescentNamedEntryReady
import OAI.Hierarchy.DescentNamedSheetAccess
import OAI.Hierarchy.DescentNamedOriginalNumberRoom
import OAI.Hierarchy.DescentNamedOriginalRootBanks
import OAI.Hierarchy.DescentPhysicalStemOperand
import OAI.Hierarchy.DescentPhysicalJointRoom

namespace OAI
/-! The real reset date uses the same finite public addresses on every input memory. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup DescentWalshPrecision
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open DescentPlainTerminal.Suffix DescentSixParty.PackedFlow.Padded ProtocolRAM
open private Hierarchy.DescentDatedAddressBook.CandidateFront.padding_end from OAI.Hierarchy.DescentPhysicalStemOperand
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
local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

local notation "front" => (v).front
local notation "bb" => S.localWalshBits p (cc+k) f (quota S.rounds)
local notation "prime₀" => (a).PrimeRoom start ((a).ingress.source floor) count (S.groupCount age) venue.degree w


local notation "early" => (v).actorEnd base₀
local notation "sp₀" => NamedEntrySpace G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w count

/-- The contact program's final marker row is the same object used to start the
three-peer phase. All these words have been issued before the masked candidate pass. -/
theorem named_marker_end
    (scene : (front).SceneRoom early ((v).issuedScene base₀ older) w) :
    ((front).donor.markers ((front).donorStart early) (v).contactShape.shapes
      (v).contactShape.markerBits).endAddress≤(v).trunkEnd base₀ :=by
  have eqn : ((front).donor.markers ((front).donorStart early) (v).contactShape.shapes
      (v).contactShape.markerBits).endAddress=(front).peers early:=rfl
  rw [eqn]
  have paid:=((front).peer_boundaries early ((v).issuedScene base₀ older) scene).2.2.2
  have scalar : (front).peer.endAddress ((front).peers early)≤(front).parentStart early:=Nat.le_add_right ..
  have parent:=(front).front_order early
  have finish : (front).mixed early ≤ (front).trunkEnd early :=
    (DescentResetTrunkCompactProgram.grow ..).trans (Nat.le_add_right ..)
  change (front).peers early≤(front).trunkEnd early
  omega

variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "I" pr:arg sc:arg => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  previousMeta previousArguments initial pr sc
local notation "ranks₀" pr:arg sc:arg => (v).linkedRankInputs (I pr sc).sectors ((v).sheetsStart base₀)

/-- Assemble all numerical pass frontiers. The three remaining checks concern only
the final seven-field operand setup and its four control columns. -/
theorem DateInputs.named_ready_of_operands
  (prepared : (rc).PreparedFits book)
  (scene : (front).SceneRoom early ((v).issuedScene base₀ older) w)
    (space : sp₀) (prime : prime₀) (stencil : (P).Room w)
    (control : (v).ControlRoom base₀ (I prepared scene).bank w)
    (placed : (v).setup.Ready (I prepared scene).bank w ((v).operandFloor base₀))
    (operands : (v).OperandEarly (I prepared scene).operand ((v).renderFromRanks (ranks₀ prepared scene) base₀) w base₀) :
    (I prepared scene).Ready := by
  obtain ⟨_,actorLimit,trunkLimit,massLimit,jointLimit,privateLimit,maskLimit,roof⟩:=(a).entered_bounds floor space.ceiling
  have rootEnd : (rc).preparedEnd book=(v).middle.stop base₀:=by rw [named_root_prepared_end (fitsStencil:=fitsStencil) (fitsSigned:=fitsSigned) (fitsCut:=fitsCut)]
  have markers:=named_marker_end G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count scene
  have groupsFit:cc≤w:=by
    have axes : cc+k≤bb :=by
      change cc+k≤DescentWalshPrecision.bits (cc+k) f (quota S.rounds) (S.censusBits p)
      unfold DescentWalshPrecision.bits; omega
    have h:=space.lookup
    have h':=space.word
    omega
  have actor:=DateInputs.fromNamed_actor_ready G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared scene prime stencil rootEnd groupsFit actorLimit
  have lanes : 0<M:=by rw [space.pitch]; exact Nat.two_pow_pos _
  have palette : 0<(front).peer.shapes:=(by decide : 0<2).trans_le (two_le_roster_card board k Ht)
  obtain ⟨header,original,rows,matched,ports,ranks⟩:=DateInputs.named_sheet_access G S board k tail age p f g drift degree
    payload e previous M nextM C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut
    count previousMeta previousArguments initial prepared scene roof
  exact {
    prime:=prime
    stencil:=stencil
    rootEnd:=rootEnd
    actor:=actor
    trunk:=trunkLimit
    donors:=markers
    mass:=massLimit
    projectionLanes:=lanes
    projectionBlocks:=Nat.two_pow_pos _
    joints:=(I prepared scene).joints_of_roof palette jointLimit
    packed:=jointLimit
    pages:=fromNamed_ready_pages G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
      previousArguments initial prepared scene
    privates:=privateLimit
    masked:=by rw [(I prepared scene).masks_end]; exact maskLimit
    numbers:=named_number_room G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
      previousArguments initial prepared scene lanes space.ceiling markers
    full:=roof
    matched:=matched
    header:=header
    original:=original
    rows:=rows
    width:=rfl
    nodes:=rfl
    slots:=rfl
    rankPorts:=ports
    ranks:=ranks
    controls:=control
    placed:=placed
    «fields»:=operands
    ordered:=DateInputs.program_order (a) (I prepared scene) }

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
