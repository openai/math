import OAI.Hierarchy.DescentNamedPanelPublicCapacity
import OAI.Hierarchy.DescentNamedOperandRequests
import OAI.Hierarchy.DescentNamedVenueMovement
import OAI.Hierarchy.DescentNamedLiveSigned
import OAI.Hierarchy.DescentNamedPrimaryValues
import OAI.Hierarchy.DescentNamedIssuedOrdinal

namespace OAI
/-! The carried archive, weighted controls and signed candidates on one reached actor state. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 2400000
set_option maxRecDepth 6144
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
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rootPhase (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w)).PreparedFits (atlasBook (namedAtlas G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) count) (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w))
  (sceneRoom : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).front.SceneRoom (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).actorEnd (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor))) (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).issuedScene (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor)) (namedOriginals G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)) w)
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

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage
local notation "priorCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal io.wire io.roster v
local notation "sourceRows" => DescentResetCanvasIngress.datedLayout input HH (v).funded.oldLanes
  (priorCPU).lanes (priorCPU).short (v).funded.precision (priorCPU).bits
local notation "oldCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal
  ((sourceRows).tokenAt floor) io.roster v
local notation "geom₀" => (a).chart start
local notation "fresh" => (geom₀).remixEnd (a).payload (a).gain (a).positive
local notation "phys₀" => DescentGLPacked.BankImage.Dated.chart (E).endAddress (geom₀).routedHosts (a).high (a).low (a).bits
local notation "saved" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((phys₀).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation "digits" => S.resetInputDigits ctl.base ctl.radix age
local notation "peer₀" => PackedFlow.portAt input.placement (input.placement.numberedHeader digits input.vertex).site

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "prev" => fun v=>(Z).placement.b (B.frame.host v)
local notation "U" => (v).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

open DescentSortedRoster DescentCompactVenuePeers DescentResetPeerUnionRAM
local notation "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "heldRoot" degreeAt:arg capAt:arg measured:arg =>
  (∃hdr : ClosedReset.Window.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
        (imageOf degreeAt capAt).book measured,
    ∃x : ClosedReset.Window.OriginalArrays B input.valid.host (v).middle.rootField,
      ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
        (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources x nBits tBits)

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
local notation "prior_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "views" degreeAt:arg => fromBoard_menu (ctl:=ctl) M p drift degree payload e previous nextM base₀ prior_ degreeAt
local notation "menuGeometry" degreeAt:arg capAt:arg => mixed_geometry (B:=B) (oldBatch:=2^e) (batch:=M) (calendar:=cal) (paid:=capAt) («v»:=v)
  (front:=(views degreeAt).1) (sheets:=(views degreeAt).2) (base:=base₀)
local notation:max "datePeerSlots" degreeProof:arg =>
  (show (v).front.peer.hosts=HH*(DescentDenseHostOrder.roster (Z).graph res (GroupStage.depthBound D n f g)).card from by
    change HH*(DescentDenseHostOrder.roster board k Ht).card=_
    rw [degreeProof]
    exact congrArg (HH*·) (calendar_palette B))
local notation "unitTicket" => originalBits D k n (GroupStage.depthBound D n f g) input.placement.cap
  (programCount board (GroupStage.depthBound D n f g)) g
open DescentSharedCableNames
local notation "A₁" => (v).receiver
local notation "G₁" => S.groupCount (age+1)
local notation "ST" => (v).sheetsStart base₀
local notation "plan" => (v).linkedRankInputs (u).sectors ST
local notation "draw" => (v).renderFromRanks plan base₀
local notation "physicalRack" => rackOf B (((Z).denseHostRank T rank).trans (Fin.castLEEmb B.next.valid.host))
open DescentResetTrunks
local notation "C₀" => (v).setup
local notation "H₁" => S.hostSize (age+1)
local notation "dense₀" => ((Z).denseHostRank T rank).trans (Fin.castLEEmb B.next.valid.host)
local notation "oldGraph" => W.granular B.count (z*G.b) B.fit
local notation "primary" t:arg => (blocks B).src (trunkParent B t)
local notation "used" => (v).operandFloor base₀
local notation "output" ok:arg m:arg => ((C₀).code used w (u).bank (u).laws).image ((u).beforeSetupImage ok m)

local notation "movementAt" => DateInputs.MovementAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
  venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
local notation "controlAt" => DateInputs.PrimaryControlsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
  venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom

include accepted in
theorem DateInputs.fromNamed_operand_panels (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (v).funded.oldLanes (v).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (v).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(v).funded.oldLanes) (oldWidth : (v).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w)
    (oldHubRoom : HH≤ io.hubs.size) (capacity : venue.cap=cap) (pitchOld : venue.lanes=2^previous)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w)
    (blocksAt : venue.k=k) (hostsAt : venue.hosts=HH) (boardRoom : h≤2^k)
    (elapsed : 0<age) (sorted : SourceSorted W input.order)

    (priorPos : 0<oldLanes)
    (newFit : S.hostSize (age+1)≤2^w) (archived : (C₀).retained.Values)
    (data : ∀j,((u).bank.old j).Fits w floor ∧ (C₀).retained.hosts*chunks (C₀).retained.groups (C₀).retained.previousLanes≤((u).bank.old j).size ∧
      Reads ((u).bank.old j) (archived j) (C₀).retained.previousLanes mem) :
    DateInputs.OperandPanelsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
      venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom degreeAt capAt ready mem archived :=by
  obtain ⟨μ,measured,dst,won,savedWord,panel,scan,posted,root,controls,R,capture,four,three,⟨rankedSource⟩⟩:=
    DateInputs.fromNamed_primary_values (B:=B) accepted drift degree payload e previous M nextM oldLanes
      primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
      initial prepared sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos
      oldWidth entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom
      capacity pitchOld chosen pitch small word ceiling blocksAt hostsAt boardRoom elapsed sorted
  have movement:=DateInputs.fromNamed_movement_at (B:=B) accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos
    oldWidth entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom
    capacity pitchOld chosen pitch small word ceiling blocksAt hostsAt priorPos newFit archived data μ measured dst won scan posted
  obtain ⟨prefixRun,cheap⟩:=DateInputs.classified_prefix («u» := (u)) ready scan posted
  have cut:=(u).run_to_sheets_from_actors ready ((entry₀).image mem) dst prefixRun cheap
  obtain ⟨hx,hj,gg,hosts,lanes,«meta»,key,before,slot,capa,deg,fit⟩:=
    fromNamed_rank_coordinates (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
      venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
      degreeAt capAt
  let ranked:=rank_sources_at B hosts lanes «meta» key physicalRack ((v).rankPorts base₀)
    (((v).rankPortPhase base₀ w).image ((u).candidateEntry ready dst)) rankedSource
  have requests:=DateInputs.requests_from_panels (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
      venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    degreeAt capAt ready archived μ measured dst movement controls
  exact ⟨μ,measured,dst,won,savedWord,panel,scan,posted,requests,R,capture,four,three,cut.1,hx,hj,gg,capa,hosts,
    calendar_candidate_read B (u) hx hj gg before slot _ ready dst ranked⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
