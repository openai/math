import OAI.Hierarchy.DescentNamedPreviousPrimitivePacket

namespace OAI
/-! # The attained root pass and its original retained-role packet -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 10000
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
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "base₀" => (a).rebased start
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
open DescentFallbackPeriod.Projected DescentPaidResidentCount.Reset DescentSixParty.ClosedReset.Window
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
local notation "im" => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "field" => (v).middle.rootField
local notation "dgr₁" => degreeAt.trans input.branch.symm
local notation "mv" => (v).roleTransfer
local notation "oldT" => (mv).transfer
local notation "geom" => DescentResetRetainedSetup.Layout.CalendarPitch.geometry (oldT)
  (show (oldT).CalendarPitch cc k payload (v).retainedRoleUnit from ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩)
local notation "inputOf" measured:arg hdr:arg x:arg => moverWindow B (im).receiver (im).book (im).prepared measured hdr x
  (mv) rfl (geom).1 B.commonDepth.symm dgr₁ capAt.symm rfl

local notation "cross" => (a).throughStencil sh start count io.hubs g (2^n) (u).src (u).sourceRows (u).oldDegree w
local notation "ticks" => (a).throughStencilTicks sh start count io.hubs g (2^n) (u).sourceRows (u).oldDegree w

local notation "rootsBefore" => (a).throughPublishedRoots (u).shape start (u).count (u).hub
  (u).g (u).Y (u).roots (u).book (u).src (u).sourceRows (u).oldDegree w (u).bookFits
local notation "rootsTime" => (a).throughPublishedTicks (u).shape start (u).count (u).hub
  (u).g (u).Y (u).roots (u).book (u).sourceRows (u).oldDegree w (u).bookFits
local notation "rootImage" measured:arg => (rc).preparedImage book prepared measured

/-- The retained role mover reads the original matrix in the memory produced by this
reset's root pass, starting from the same stencil execution as the input packet. -/
theorem DateInputs.fromNamed_inherited_root (ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) (capacity : venue.cap=cap)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (before measured : Memory w) (hdr : OriginalHeader B input.valid.host (im).receiver (im).book measured)
    (x : OriginalArrays B input.valid.host field)
    (issued : RootPacket B (im).receiver (im).book (im).prepared measured hdr (im).sources x nBits tBits)
    (scan : (cross).Exec before measured ticks) :
    (rootsBefore).Exec before (rootImage measured) rootsTime ∧
      Source (FinalInputs.oldMatrix u) (inputOf measured hdr x) (mv).rootLanes (rootImage measured) := by
  constructor
  · intro P R K machine
    exact Procedure.Exec.then scan ((rc).prepared_any book prepared measured).1 machine
  · exact DateInputs.fromNamed_primitive_packet (B:=B) drift degree payload e previous M nextM
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
      previousMeta previousArguments initial prepared sceneRoom degreeAt capAt ready chosen pitch
      small word ceiling capacity gr fee measured hdr x issued

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
