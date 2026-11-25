import OAI.Hierarchy.DescentNamedOriginalHeader
import OAI.Hierarchy.DescentNamedReindexedBanks
import OAI.Hierarchy.DescentCalendarSenderCoordinates

namespace OAI
/-! # The named date reads the actual previously measured root and actor banks -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
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
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
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
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

open DescentFallbackPeriod.Projected DescentPaidResidentCount.Reset
local notation "sources" => atlasSender atlas sh start count io.hubs g (2^n) roots w
local notation "middle" => (v).middle
local notation "X₀" => Receiver.IndexedRoots.mk (rc) (book) prepared (sources)
local notation "fac" => 32*Nat.clog 2 (2*venue.degree)
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)

local notation "im" => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt

open CandidateFront DescentResetNewActorDirectory DescentResetLocalRoster
local notation "layout" => (v).actor.directory actorBase
local notation "scene" => (v).actor.scene actorBase
local notation "rootsAt" => EarlierBanks.fromRoot (im).receiver (im).book (im).sources
  (atlas).hostIndex io.hubs layout scene
local notation "priorAt" => EarlierBanks.castTo input.branch (ClosedReset.Window.calendar_residual B) capAt B.dimension rootsAt
local notation "old" => namedSenderBanks G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "meta" => (CandidateSheets.fromBoard S board k tail age D f g cap M).metaBits
local notation "realFront" => setupFront S board k tail age D f g (2^e) M
  (ResetMiddle.fieldWidth D cap n k (GroupStage.depthBound D n f g)) meta C packet cal
local notation "actualOld" => calendarOriginals S board k tail age D f g (2^e) M
  (ResetMiddle.fieldWidth D cap n k (GroupStage.depthBound D n f g)) meta C packet cal early priorAt

theorem fromNamed_calendar_banks : HEq old priorAt:=by
  subst D
  let half : (a).c/2=cap:=by change (2*cap)/2=cap;omega
  have common:=(X₀).earlier_eq input.branch.symm (half.trans capAt.symm) B.dimension.symm
    (ClosedReset.Window.calendar_residual B).symm B.commonDepth.symm rfl
    (S.group_power ctl.base ctl.radix age) rfl
    input.branch (ClosedReset.Window.calendar_residual B) capAt B.dimension (atlas).hostIndex io.hubs layout scene
  apply heq_of_eq
  change cast (congrArg (fun t=>EarlierBanks venue.degree k t n) half)
    (EarlierBanks.fromRoot (X₀).receiver (X₀).book (X₀).sources (atlas).hostIndex io.hubs layout scene)=_
  exact (EarlierBanks.cap_cast _ half).symm.trans common.symm

/-- The stream of original row operands in the named date is the one acquired
from the reindexed receiver, its measured root data, and the executed actor directory. -/
theorem fromNamed_calendar_originals : HEq (u).earlier actualOld:=by
  have h:=fromNamed_sender_banks G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared sceneRoom
  subst D
  have eqn:=eq_of_heq (fromNamed_calendar_banks (B:=B) drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared rfl capAt)
  rw [←eqn]
  exact h

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
