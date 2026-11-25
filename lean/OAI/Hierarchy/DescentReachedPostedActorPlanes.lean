import OAI.Hierarchy.DescentNamedCensusPacketLimits
import OAI.Hierarchy.DescentAttainedPostedActorPlanes
import OAI.Hierarchy.DescentNamedPacketRankRead

namespace OAI
/-! # A physical reset posts its recorded venue and its actor event in the shared history -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM DescentDatedAddressBook DescentSixParty.ClosedReset.Window DescentFundedCensus DescentPaidResidentCount.Reset
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentFallbackPeriod.Projected
open DescentResetLocalRoster DescentResetFieldAssembler DescentResetCandidatePair DescentResetRankedWindows
open DescentSortedRoster DescentResetPeerUnionRAM DescentCompactVenuePeers DescentSixParty.Chronology
open DescentSixParty.ClosedReset DescentGL DescentIssuedFallbackPanel
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

local notation "inputs" => FinalInputs.predecessor dateInput
local notation "actorRows" => HH*chunks (2^(T).commonDepth) (2^e)


variable (run : (dateInput).FinalInputs)
local notation "st_" => (a).throughStencil (dateInput).shape start (dateInput).count (dateInput).hub (dateInput).g (dateInput).Y
  (dateInput).src (dateInput).sourceRows (dateInput).oldDegree w
local notation "time_" => (a).throughStencilTicks (dateInput).shape start (dateInput).count (dateInput).hub (dateInput).g (dateInput).Y
  (dateInput).sourceRows (dateInput).oldDegree w
local notation "fund_" => (namedSuccessor).funded
local notation "bill_" => (namedSuccessor).venue.census
local notation "precision" => (bill_).bits
local notation "key_" => (⟨(P).saved,0⟩:Bank)
local notation "feeStart" => (namedSuccessor).fundedEnd base₀
local notation "feeBanks" => fundedPorts (funded_residual B) B.dimension run.ports
local notation "paidRAM" dst:arg => DescentFundedCensus.memory run.jobs feeStart
  ((fund_).memory ((namedSuccessor).finalEnd base₀) run.earlier key_ dst)
local notation "enter" src:arg => (entry₀).image src
local notation "atOps" src:arg => (dateInput).throughOperandDate.nextMemory (enter src)
local notation "oldRaw" => input.vertex.trans (Fin.castLEEmb input.valid.host)


variable [Fintype X]
variable (padDate : Chronology.NativePhase w) (calendar : ℕ→DateCode w) (boot : Memory w)
local notation "mem₀" => padDate.image (DateCode.history calendar boot age)
local notation "HH₁" => S.hostSize (age+1)
local notation "st" => (namedSuccessor).sheetsStart base₀
local notation "ms" => (namedSuccessor).sheets
local notation "hs" => (dateInput).sectors.pageBits
local notation "dense" => B.next.vertex.trans (Fin.castLEEmb B.next.valid.host)
local notation "trueRank" => (Z).rawHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb input.valid.host))
local notation "depth" => GroupStage.depthBound D n f g
local notation "program" => programCount ctl.board depth
local notation "dgt" => originalBits D k n depth input.placement.cap program g
local notation "tg" => (inputs).tag
variable {U₀ U₁ : MarkedWorld F d X abits} {z₀ D₀ len zl Dl : ℕ}
    {first : Reached U₀ G q ε S k 0 z₀ D₀ wire hist} {last : Reached U₁ G q ε S k len zl Dl wire hist}
    {path : Path first last} (priorPath : Path first input) (tailPath : Path B.next last)
    (eventAt : (priorPath.reset B).append tailPath=path)
local notation "event_" => (Path.Event.reset priorPath B tailPath eventAt : path.Event age)

local notation "rootDeck" h:arg c:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared h c

omit [Fintype X] in
private theorem transport_rank_rack {allocatedHosts scheduledHosts : ℕ}
    (same : allocatedHosts = scheduledHosts) (pad : Fintype.card input.V ≤ S.hostSize age)
    (bound : Fintype.card B.next.V ≤ scheduledHosts)
    (family : (h : ℕ) → (Fin h → Option B.next.V) → Prop)
    (observed : family scheduledHosts (rackOf B (((Z).denseHostRank T
      ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)))) :
    family allocatedHosts (rackOf B (B.next.vertex.trans (Fin.castLEEmb (bound.trans_eq same.symm)))) := by
  subst allocatedHosts
  exact (congrArg (family scheduledHosts) (packet_rank_rack (B:=B) pad bound)).mp observed

include accepted in
omit [Fintype X] in
theorem DateInputs.fromNamed_venue_and_last_actors (degreeAt : venue.degree=D) (ready : (dateInput).Ready)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (namedSuccessor).funded.oldLanes (namedSuccessor).funded.precision floor
      (input.venueRoster input.valid.host) mem₀) (popFit : count.Fits w floor)
    (popRead : mem₀ count.base=(Fintype.card input.V:Word w))
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
    (hosts : HH=venue.hosts) (groups : venue.groups=S.groupCount age)
    (blocks : venue.k=k) (capacity : venue.cap=input.placement.cap) (pitch : venue.lanes=2^previous)
    (pos : 0<M) (readLanes : (fund_).oldLanes=venue.lanes) (readBits : (fund_).precision=precision)
    (original : run.io=io) (safe : run.Room) (banks : IssuedBanks io venue.hosts (S.groupCount age) venue.lanes)
    (oldHub : io.hubs.Fits w floor) (oldAtom : ∀x:Fin (2^(a).ingress.k),(io.atoms x.val).Fits w floor)
    (oldWire : ∀j:(a).ingress.signed.Slot,(io.wire j.1.val j.2.val).Fits w floor)
    (chosenCut : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (rootLanes : M=2^e) (narrow : 8*(namedSuccessor).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) (heightRoom : depth+2<w)
    (positiveQuota : 0<quota S.rounds) (countFits : amp<2^precision) (arrivalFits : 2*input.placement.cap<2^precision)
    (posted : calendar age=DateCode.withPriorArchive padDate (PhysicalReset.enterCode (a).ingress floor (dateInput) run io))
    (padded : padDate.Runs (DateCode.history calendar boot age))
    (nextHost : 0<HH₁) (nextChunks : 0<chunks (S.groupCount (age+1)) M)
    (peerSize : (namedSuccessor).front.peer.hosts=HH*rows)
    (allocated : (ms).hosts=HH₁) (emitLanes : (namedSuccessor).receiver.lanes=M)
    (oldHubRoom : HH≤ io.hubs.size) (boardRoom : h≤2^k) (elapsed : 0<age) (sorted : SourceSorted W input.order) :
    (DatePorts.reset a start dateInput).held B.next ((a).endAddress start) (DateCode.history calendar boot (age+1)) ∧
    (nextM=S.groupCount (age+1) → (event_).actorPlanes (fun x=>(namedSuccessor).terminalActor base₀ x.val) (DateCode.history calendar boot (age+1))):=by
  obtain ⟨up,one,enough,legal⟩:=posted_actor_packet_limits B p gr fee branch
  obtain ⟨μ,measured,dst,won,savedAt,panel,scan,post,rootProof,R,observed,four,near,ranks⟩:=
    DateInputs.fromNamed_rank_sources accepted drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom degreeAt ready mem₀ gr fee capAt history branch seen popFit popRead wireRoom oldPos
      oldWidth entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom
      oldHubRoom (capacity.trans capAt) pitch chosenCut rootLanes narrow word ceiling blocks hosts.symm boardRoom elapsed sorted
  apply DateInputs.recorded_posted_planes accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom run padDate calendar boot priorPath tailPath eventAt degreeAt ready gr fee capAt history
    branch seen popFit popRead wireRoom oldPos oldWidth entryFits low score live degreePos headerBits hostBits ranksFit
    namesFit degFit laneRoom hosts groups blocks capacity pitch pos readLanes readBits original safe banks oldHub oldAtom
    oldWire chosenCut rootLanes narrow word ceiling heightRoom up one enough legal positiveQuota countFits
    arrivalFits posted padded nextHost nextChunks peerSize allocated emitLanes
  refine ⟨μ,measured,dst,won,savedAt,panel,scan,post,rootProof,R,observed,four,near,?_⟩
  exact transport_rank_rack (B:=B) allocated input.valid.host B.next.valid.host
    (fun hostCount rack => Nonempty (RankSources B (b:=(ms).metaBits) (t:=dgt) (M:=(ms).lanes)
      (H:=hostCount) rack ((namedSuccessor).rankPorts base₀) (sheetHeader B st hs) (sheetOriginal B st hs)
      (((namedSuccessor).rankPortPhase base₀ w).image ((dateInput).before_ports ready dst)))) ranks

-- Explicit packet bounds belong to this entry point even though the recorded
-- venue theorem derives them from the schedule.
include accepted in
omit [Fintype X] in
theorem DateInputs.fromNamed_recorded_posted_planes (degreeAt : venue.degree=D) (ready : (dateInput).Ready)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (namedSuccessor).funded.oldLanes (namedSuccessor).funded.precision floor
      (input.venueRoster input.valid.host) mem₀) (popFit : count.Fits w floor)
    (popRead : mem₀ count.base=(Fintype.card input.V:Word w))
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
    (hosts : HH=venue.hosts) (groups : venue.groups=S.groupCount age)
    (blocks : venue.k=k) (capacity : venue.cap=input.placement.cap) (pitch : venue.lanes=2^previous)
    (pos : 0<M) (readLanes : (fund_).oldLanes=venue.lanes) (readBits : (fund_).precision=precision)
    (original : run.io=io) (safe : run.Room) (banks : IssuedBanks io venue.hosts (S.groupCount age) venue.lanes)
    (oldHub : io.hubs.Fits w floor) (oldAtom : ∀x:Fin (2^(a).ingress.k),(io.atoms x.val).Fits w floor)
    (oldWire : ∀j:(a).ingress.signed.Slot,(io.wire j.1.val j.2.val).Fits w floor)
    (chosenCut : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (rootLanes : M=2^e) (narrow : 8*(namedSuccessor).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) (heightRoom : depth+2<w)
    (_up : cc+k-(T).commonDepth<2^nBits) (_one : 1<2^nBits) (_enough : 2^(cc+k-(T).commonDepth)*amp<2^nBits)
    (_legal : 2*DescentFallbackShapeTable.rows (cc+k-(T).commonDepth) (2^(Z).n)≤2^tBits)
    (positiveQuota : 0<quota S.rounds) (countFits : amp<2^precision) (arrivalFits : 2*input.placement.cap<2^precision)
    (posted : calendar age=DateCode.withPriorArchive padDate (PhysicalReset.enterCode (a).ingress floor (dateInput) run io))
    (padded : padDate.Runs (DateCode.history calendar boot age))
    (lastLanes : nextM=S.groupCount (age+1)) (nextHost : 0<HH₁) (nextChunks : 0<chunks (S.groupCount (age+1)) M)
    (peerSize : (namedSuccessor).front.peer.hosts=HH*rows)
    (allocated : (ms).hosts=HH₁) (emitLanes : (namedSuccessor).receiver.lanes=M)
    (oldHubRoom : HH≤ io.hubs.size) (boardRoom : h≤2^k) (elapsed : 0<age) (sorted : SourceSorted W input.order) :
    (DatePorts.reset a start dateInput).held B.next ((a).endAddress start) (DateCode.history calendar boot (age+1)) ∧
    (event_).actorPlanes (fun x=>(namedSuccessor).terminalActor base₀ x.val) (DateCode.history calendar boot (age+1)):=by
  have result:=DateInputs.fromNamed_venue_and_last_actors accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom run padDate calendar boot priorPath tailPath eventAt degreeAt ready gr fee capAt history
    branch seen popFit popRead wireRoom oldPos oldWidth entryFits low score live degreePos headerBits hostBits ranksFit
    namesFit degFit laneRoom hosts groups blocks capacity pitch pos readLanes readBits original safe banks oldHub oldAtom
    oldWire chosenCut rootLanes narrow word ceiling heightRoom positiveQuota countFits arrivalFits
    posted padded nextHost nextChunks peerSize allocated emitLanes oldHubRoom boardRoom elapsed sorted
  exact ⟨result.1,result.2 lastLanes⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
