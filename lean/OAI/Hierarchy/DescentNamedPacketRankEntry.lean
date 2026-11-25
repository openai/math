import OAI.Hierarchy.DescentNamedVenuePostedBasis
import OAI.Hierarchy.DescentNamedCalendarRootPacket
import OAI.Hierarchy.DescentNamedCaptureRoster

namespace OAI
/-! # The selected root packet and the exact memory at the rank inputs -/
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
  (venue : StageVenueTail.Date) (io : Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "namedSuccessor" => (a).successor
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
local notation "actorBase" => (namedSuccessor).middle.stop base₀
local notation "early" => (namedSuccessor).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (namedSuccessor).front.SceneRoom early ((namedSuccessor).issuedScene base₀ older) w)
local notation "dateInput" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage
local notation "priorCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal io.wire io.roster namedSuccessor
local notation "sourceRows" => DescentResetCanvasIngress.datedLayout input HH (namedSuccessor).funded.oldLanes
  (priorCPU).lanes (priorCPU).short (namedSuccessor).funded.precision (priorCPU).bits
local notation "oldCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal
  ((sourceRows).tokenAt floor) io.roster namedSuccessor
local notation "geom₀" => (a).chart start
local notation "fresh" => (geom₀).remixEnd (a).payload (a).gain (a).positive
local notation "phys₀" => DescentGLPacked.BankImage.Dated.chart (E).endAddress (geom₀).routedHosts (a).high (a).low (a).bits
local notation "saved" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((phys₀).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation "digits" => S.resetInputDigits ctl.base ctl.radix age
local notation "peer₀" => PackedFlow.portAt input.placement (input.placement.numberedHeader digits input.vertex).site

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (DescentDenseHostOrder.roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "prev" => fun v=>(Z).placement.b (B.frame.host v)
local notation "U" => (namedSuccessor).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (dateInput).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (dateInput).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

open DescentSortedRoster
local notation:max "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation:max "heldRoot" degreeAt:arg capAt:arg measured:arg =>
  (∃hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
        (imageOf degreeAt capAt).book measured,
    ∃x : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host (namedSuccessor).middle.rootField,
      ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
        (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources x nBits tBits)
set_option maxHeartbeats 750000 in
include accepted in
theorem DateInputs.fromNamed_packet_entry (degreeAt : venue.degree=D) (ready : (dateInput).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (namedSuccessor).funded.oldLanes (namedSuccessor).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (namedSuccessor).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(namedSuccessor).funded.oldLanes) (oldWidth : (namedSuccessor).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w)
    (oldHubRoom : HH≤ io.hubs.size) (capacity : venue.cap=cap) (pitchOld : venue.lanes=2^previous)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(namedSuccessor).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) :
    ∃(μ : DescentGL.Layout (E).dim) (measured dst : Memory w),HEq μ B.frame.basis ∧
      measured (P).saved=((DescentExterior.matrixCode μ).val:Word w) ∧
      (∀x<floor,measured x=mem x) ∧
      ClosedReset.Recorded.StencilReservationWords (reset:=B) E ((sh).dimension.symm.trans B.keyWidth.symm)
        venue.degree degreeAt.symm.le measured ∧
      (P).S.OldOrder (P).X (P).base (P).bank g (T).commonDepth μ measured ∧
      ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
        count (E).depthRows (rc).stencil book measured ∧
      ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
        ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      (pub).Exec measured dst ticks ∧
      ((((entry₀).program.seq ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w)).seq pub)).Exec mem dst
          (((entry₀).ticks+(a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w)+ticks) ∧
      dst (dir).count.base=(Fintype.card B.next.V:Word w) ∧
      (∀v : B.next.V,dst ((dir).inverse.base+((Z).denseHostRank T rank v).val)=((rawId v).val:Word w)) ∧
      (∀v : B.next.V,dst ((dir).ranks.base+(rawId v).val)=(((Z).denseHostRank T rank v).val:Word w)) ∧
      (∀j : Fin (HH*rows),dst ((dir).flags.base+j.val)=if ∃v,rawId v=j then 1 else 0) ∧
      (∀j,j < (rc).origin ∨ (dir).endAddress ≤ j → dst j=measured j) ∧
      heldRoot degreeAt capAt measured ∧ ClosedReset.Window.PostedStemBasis B dateInput dst ∧
      ∃mid,dst=(dir).result scene mid ∧
        (dateInput).earlier.oldRoster.Fits w actorBase ∧ HH*input.placement.degree≤(dateInput).earlier.oldRoster.size ∧
        (∀(a₀:Fin HH) (j:Fin input.placement.degree),mid
          ((dateInput).earlier.oldRoster.base+(a₀.val*input.placement.degree+j.val))=
          (target (DescentPacking.PackedMatch.Local.Stage.hostRotor idx (DescentGroupPeerOrder.hostRoster input.placement
            ((idx).trans Fin.valEmbedding)) a₀ j):Word w)) ∧
        (∀j (p₀ : Row HH (2^(T).commonDepth) (2^e)),mid ((scene).base+j.val*(HH*chunks (2^(T).commonDepth) (2^e))+
          (row _ _ _ p₀).val)=((data (ClosedReset.Recorded.realActor (reset:=B) (ClosedReset.Window.shapes B)
            (ClosedReset.Window.rack B input.valid.host) j) p₀).val:Word w)) ∧
        (∀j,j < actorBase → mid j=(rc).preparedImage book prepared measured j) ∧
        (∀v,mid (((U).depths actorBase).base+(idx v).val)=(prev v:Word w)) ∧
        (∀j,j < ((U).levels actorBase).size → mid (((U).levels actorBase).base+j)=((j-(T).commonDepth+1:ℕ):Word w)) ∧
        (∀v,mid (io.hubs.base+(idx v).val)=((input.placement.hub v).toNat:Word w)) ∧
        ∀v,dst (io.hubs.base+(idx v).val)=((input.placement.hub v).toNat:Word w) :=by
  obtain ⟨μ,measured,dst,won,savedWord,kept,reserved,order,panel,issued,act,whole,ct,inv,fwd,flags,lowDst,
      mid,post,occupied,rootRows,depths,levels,midHub,dstHub⟩:=
    DateInputs.fromNamed_venue_matrix accepted drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos
      oldWidth entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom
  have rootsHeld:=DateInputs.fromNamed_calendar_root_packet (B:=B) accepted drift degree payload e previous M
    nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom degreeAt capAt ready mem measured gr fee branch seen wireRoom
    oldHubRoom hostBits degFit namesFit chosen pitch small word ceiling capacity pitchOld score headerBits live
    degreePos μ won savedWord kept reserved order panel
  have rosters:=DateInputs.fromNamed_capture_roster (B:=B) drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom degreeAt ready mem measured mid seen kept μ order rootRows
  have basis:=ClosedReset.Window.stem_posted_basis B dateInput ready measured dst μ ((sh).dimension.symm.trans B.keyWidth.symm)
    won savedWord (fun j hj=>lowDst j (.inl hj))
  exact ⟨μ,measured,dst,won,savedWord,kept,reserved,order,panel,issued,act,whole,ct,inv,fwd,flags,lowDst,
    rootsHeld,basis,mid,post,rosters.1,rosters.2.1,rosters.2.2,occupied,rootRows,depths,levels,midHub,dstHub⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
