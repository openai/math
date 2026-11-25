import OAI.Hierarchy.DescentNamedEarlierPlacement
import OAI.Hierarchy.DescentDatedHomeBook
import OAI.Hierarchy.DescentEarlierMoverPacket
import OAI.Hierarchy.DescentDatedRolePriorFrames
import OAI.Hierarchy.DescentDatedRetainedPitches

namespace OAI
/-! # Both original source archives enter the dated retained-role transfer -/
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
open DescentGL DescentGroupPeerOrder DescentFallbackRankRAM
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
local notation "fac" => 32*Nat.clog 2 (2*venue.degree)
local notation "staged" => fromNamed_matrix_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "im" => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
open DescentPlainTerminal.Suffix DescentPacking.PackedMatch.Local.Stage.Chooser
local notation "head" => (P).S.header (P).base
local notation "field" => (v).middle.rootField
local notation "mid" m₀:arg => (im).receiver.preparedMid (im).book (im).prepared m₀
local notation "ceil" => (im).receiver.headerEnd (im).book
local notation "depths" => ClosedReset.Recorded.oldDepth B
local notation "coarse" => (T).commonDepth
local notation "span" => (Z).k-coarse
local notation "cat" => RootTemplates.arena ceil HH (2^coarse) (2^e) span (Z).n input.placement.degree
local notation "pop" => Fintype.card input.V


open DescentSixParty.ClosedReset.Window
open DescentOperandRootPull
local notation "A₁" => input.placement
local notation "C₁" => (v).setup
local notation "M₁" => 2^e
local notation "done₁" m₀:arg => (rc).preparedImage book prepared m₀
local notation "cargo" X₁:arg m₀:arg hdr₁:arg => calendar_sender_matrix B M₁ field (im).receiver (im).book (im).prepared m₀ hdr₁ X₁
local notation "slot₁" => 2*(A₁).cap
local notation "dgr₁" => degreeAt.trans input.branch.symm
local notation "half₁" => (show (a).c/2=cap by change (2*cap)/2=cap;omega)
local notation "cw₁" => half₁.trans capAt.symm
local notation "rn₁" => (calendar_residual B).symm
local notation "book₀" => Receiver.IndexedRoots.mk (rc) (book) prepared (sources)


local notation "mv" => (v).roleTransfer
local notation "oldT" => (mv).transfer
local notation "geom" => DescentResetRetainedSetup.Layout.CalendarPitch.geometry (oldT)
  (show (oldT).CalendarPitch cc k payload (v).retainedRoleUnit from ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩)
local notation "inputOf" measured:arg hdr:arg x:arg => moverWindow B (im).receiver (im).book (im).prepared measured hdr x
  (mv) rfl (geom).1 B.commonDepth.symm dgr₁ capAt.symm rfl

/-- The same prepared source used for seven retained pointer fields supplies the retained
primitive role. Every low source block and both measured hole tests are preserved. -/
theorem DateInputs.fromNamed_primitive_packet (ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) (capacity : venue.cap=cap)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (measured : Memory w) (hdr : OriginalHeader B input.valid.host (im).receiver (im).book measured)
    (x : OriginalArrays B input.valid.host field)
    (issued : RootPacket B (im).receiver (im).book (im).prepared measured hdr (im).sources x nBits tBits) :
    Source (FinalInputs.oldMatrix u) (inputOf measured hdr x) (mv).rootLanes (done₁ measured):=by
  obtain ⟨rows,signal,packetRead,signedRead,original,_⟩:=DateInputs.fromNamed_earlier_placement (B:=B) drift degree payload
    e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared sceneRoom degreeAt capAt ready chosen pitch small word ceiling
    capacity gr fee measured hdr x issued
  have donors : (oldT).donors=(C₁).retained.donors :=
    (geom).2.1.trans (show (oldT).blocks=(C₁).retained.donors from (u).menu.donors.symm)
  have width : (mv).control.rootWidth=(C₁).seven.control.rootWidth :=by
    change field*DescentRotorWindowArchive.count venue.degree (oldT).donors cap=
      field*DescentRotorWindowArchive.count venue.degree (C₁).retained.donors cap
    rw [donors]
  apply FinalInputs.source_axes _ _ rfl rfl width rfl rows _ packetRead
  intro host coarseGroup
  exact (original host coarseGroup).symm

variable (zFinal : (u).FinalInputs)
local notation "cross" => (a).throughStencil sh start count io.hubs g (2^n) (u).src (u).sourceRows (u).oldDegree w
local notation "ticks" => (a).throughStencilTicks sh start count io.hubs g (2^n) (u).sourceRows (u).oldDegree w

include degreeAt in
/-- The actual date uses this small fixed home-key table for every packed recipient. -/
theorem FinalInputs.fromNamed_home_book
    (dim : (mv).shapes=(roster ctl.board k (GroupStage.depthBound D n f g)).card) :
    zFinal.which=fun j=>DescentResetActorClass.targetBook ctl.board k (GroupStage.depthBound D n f g) (j.cast dim):=by
  apply zFinal.which_calendar ctl.board k _ rfl rfl HEq.rfl rfl _ dim
  exact congrArg (fun arity=>GroupStage.depthBound arity n f g) degreeAt

/-- The earlier semantic source is recovered from a single selected root packet. It remains live
after the complete native operand, paid-census and compact-venue passes. -/
theorem FinalInputs.fromNamed_prior_matrix (ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) (capacity : venue.cap=cap)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (before measured mid₀ : Memory w) (hdr : OriginalHeader B input.valid.host (im).receiver (im).book measured)
    (x : OriginalArrays B input.valid.host field)
    (issued : RootPacket B (im).receiver (im).book (im).prepared measured hdr (im).sources x nBits tBits)
    (fit : zFinal.Room) (prefixRun : (cross).Exec before measured ticks)
    (operands : (u).throughOperandDate.Runs before mid₀) :
    Source (FinalInputs.oldMatrix u) (inputOf measured hdr x) (mv).rootLanes (zFinal.venueImage mid₀):=by
  have gathered:=DateInputs.fromNamed_primitive_packet (B:=B) drift degree payload e previous M nextM oldLanes
      primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
      previousArguments initial prepared sceneRoom degreeAt capAt ready chosen pitch small word ceiling
      capacity gr fee measured hdr x issued
  apply zFinal.original_matrix_source ready fit («roots»:=done₁ measured) _ operands _ gathered
  intro prog regs mem machine
  exact Procedure.Exec.then prefixRun ((rc).prepared_any book prepared measured).1 machine

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
