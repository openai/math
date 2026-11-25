import OAI.Hierarchy.DescentCapturedActorEvent
import OAI.Hierarchy.DescentNamedCapturedActorBounds
import OAI.Hierarchy.DescentOriginalCapturedRanks
import OAI.Hierarchy.DescentNamedStemSector

namespace OAI
/-! # Posted actor venue from a named reset with its measured original input packet -/
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
  (venue : StageVenueTail.Date) (io : Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "successor₀" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
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
local notation "actorBase" => (successor₀).middle.stop base₀
local notation "early" => (successor₀).actorEnd base₀

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
local notation "priorCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal io.wire io.roster successor₀
local notation "sourceRows" => DescentResetCanvasIngress.datedLayout input HH (successor₀).funded.oldLanes
  (priorCPU).lanes (priorCPU).short (successor₀).funded.precision (priorCPU).bits
local notation "oldCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal
  ((sourceRows).tokenAt floor) io.roster successor₀
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
local notation "U" => (successor₀).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

local notation "inputs" => FinalInputs.predecessor u
local notation "actorRows" => HH*chunks (2^(T).commonDepth) (2^e)


variable (run : @FinalInputs (named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) w ((DateInputs.fromNamed G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count) previousMeta previousArguments initial prepared sceneRoom))
local notation "st_" => (a).throughStencil (u).shape start (u).count (u).hub (u).g (u).Y
  (u).src (u).sourceRows (u).oldDegree w
local notation "time_" => (a).throughStencilTicks (u).shape start (u).count (u).hub (u).g (u).Y
  (u).sourceRows (u).oldDegree w
local notation "fund_" => (successor₀).funded
local notation "bill_" => (successor₀).venue.census
local notation "precision" => (bill_).bits
local notation "key_" => (⟨(P).saved,0⟩:Bank)
local notation "feeStart" => (successor₀).fundedEnd base₀
local notation "feeBanks" => fundedPorts (funded_residual B) B.dimension run.ports
local notation "paidRAM" dst:arg => DescentFundedCensus.memory run.jobs feeStart
  ((fund_).memory ((successor₀).finalEnd base₀) run.earlier key_ dst)
local notation "enter" src:arg => (entry₀).image src
local notation "atOps" src:arg => (u).throughOperandDate.nextMemory (enter src)
local notation "oldRaw" => input.vertex.trans (Fin.castLEEmb input.valid.host)


variable [Fintype X]
variable (padDate : Chronology.NativePhase w) (calendar : ℕ→DateCode w) (boot : Memory w)
local notation "mem₀" => padDate.image (DateCode.history calendar boot age)
local notation "HH₁" => S.hostSize (age+1)
local notation "st" => (successor₀).sheetsStart base₀
local notation "ms" => (successor₀).sheets
local notation "hs" => (u).sectors.pageBits
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

omit [Fintype X] in
theorem packet_rank_rack {H₀ H₁ : ℕ} (pad : Fintype.card input.V≤H₀) (bound : Fintype.card B.next.V≤H₁) :
    rackOf B (((Z).denseHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))).trans
      (Fin.castLEEmb bound))=rackOf B (B.next.vertex.trans (Fin.castLEEmb bound)):=by
  apply congrArg (rackOf B)
  ext v
  change ((Z).denseHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad)) v).val=
    ((Z).denseHostRank T (B.frame.host.symm.toEmbedding.trans input.vertex) v).val
  rw [(Z).denseHostRank_read,(Z).denseHostRank_read]
  rfl

omit [Fintype X] in
/-- Lookup-invariant coindexing of the dense host ordinal. -/
private theorem coindex_actor_rack {J J' : ℕ} (r : Fintype.card B.next.V≤J) (r' : Fintype.card B.next.V≤J')
    (eqn : J'=J) : (fun v : Fin J'=>rackOf B (B.next.vertex.trans (Fin.castLEEmb r)) (v.cast eqn))=
      rackOf B (B.next.vertex.trans (Fin.castLEEmb r')):=by subst J';rfl

include accepted in
set_option maxHeartbeats 800000 in
omit [Fintype X] in
theorem DateInputs.fromNamed_posted_actor_event (degreeAt : venue.degree=D) (ready : (u).Ready)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (successor₀).funded.oldLanes (successor₀).funded.precision floor
      (input.venueRoster input.valid.host) mem₀) (popFit : count.Fits w floor)
    (popRead : mem₀ count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (successor₀).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(successor₀).funded.oldLanes) (oldWidth : (successor₀).funded.precision=S.censusBits p)
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
    (measured : Memory w) (scan : (st_).Exec (enter mem₀) measured time_)
    (μ : DescentGL.Layout ((cc-e)+(e+k))) (chosen : HEq μ B.frame.basis)
    (saved_ : measured (P).saved=((DescentExterior.matrixCode μ).val:Word w))
    (snap : PaddedSnapshot B (input.valid.host.trans_eq hosts) (u).roots.field)
    (rootPages : ∀s t,Source ((feeBanks).bank s t) (savedInput B (input.valid.host.trans_eq hosts) snap) (2^e)
      ((rc).preparedImage (u).book (u).bookFits measured))
    (fBits : ℕ)
    (printed : PackedFlow.Padded.Published (h:=cc-e) (l:=e+k) (2^e) (P).S.t (P).output
      (input.vertex.trans (Fin.castLEEmb (input.valid.host.trans_eq hosts)))
      (ClosedReset.Recorded.realPanel (reset:=B) (by omega : cc-e+(e+k)=cc+k) μ fBits (P).S.t) measured)
    (up : cc+k-(T).commonDepth<2^fBits) (one : 1<2^fBits) (enough : 2^(cc+k-(T).commonDepth)*amp<2^fBits)
    (legal : 2*DescentFallbackShapeTable.rows (cc+k-(T).commonDepth) (2^(Z).n)≤2^(P).S.t)
    (positiveQuota : 0<quota S.rounds) (countFits : amp<2^precision) (arrivalFits : 2*input.placement.cap<2^precision)
    (posted : calendar age=DateCode.withPriorArchive padDate (PhysicalReset.enterCode (a).ingress floor (u) run io))
    (padded : padDate.Runs (DateCode.history calendar boot age))
    (nextHost : 0<HH₁) (nextChunks : 0<chunks (S.groupCount (age+1)) M)
    (actorMem : Memory w) (published : (pub).Exec measured actorMem ticks)
    (peerSize : (successor₀).front.peer.hosts=HH*rows)
    (allocated : (ms).hosts=HH₁) (emitLanes : (successor₀).receiver.lanes=M)
    (captured :
      ∃ R : (u).MeasuredChannels (Fintype.card B.next.V),PhysicalReset.DateInputs.CaptureRoom R actorMem ∧
       (∀s:B.next.V,present (selfPeers (renumberPeer peerSize R.near)) (trueRank s)=
          (insert s ((Z).emittedNear T s)).map trueRank) ∧
       (∀s:B.next.V,present (renumberPeer peerSize R.near) (trueRank s)=((Z).emittedNear T s).map trueRank) ∧
       Nonempty (RankSources B (b:=(ms).metaBits) (t:=dgt) (M:=(ms).lanes)
         (rackOf B (B.next.vertex.trans (Fin.castLEEmb (B.next.valid.host.trans_eq allocated.symm))))
         ((successor₀).rankPorts base₀) (sheetHeader B st hs) (sheetOriginal B st hs)
         (((successor₀).rankPortPhase base₀ w).image ((u).before_ports ready actorMem)))) :
    (DatePorts.reset a start u).held B.next ((a).endAddress start) (DateCode.history calendar boot (age+1)) ∧
    (nextM=S.groupCount (age+1) → (event_).actorPlanes (fun x=>(successor₀).terminalActor base₀ x.val) (DateCode.history calendar boot (age+1))):=by
  obtain ⟨calibrated,rawSize,used,word,rawActor,rankEarly,inverseEarly,forwardEarly,peerEarly,rankFits,peerFits,
    paidEnd,actorsEnd,wireEnd⟩:=DateInputs.fromNamed_held_bounds B p drift degree payload e previous M nextM
      oldLanes primitiveLanes printedBits venue io floor w (u) ready degreeAt blocks hosts.symm capAt pos
  obtain ⟨hx,hj,gg,sameHosts,sameLanes,«meta»,keys,comp,slot,capacityAt,roleDegree,actorDigits⟩:=
    fromNamed_rank_coordinates (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
      venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
      degreeAt capAt
  obtain ⟨R,read,four,near,⟨earned⟩⟩:=captured
  let shost:=B.next.valid.host.trans_eq allocated.symm
  have tickets:=rank_sources_at B sameHosts sameLanes «meta» keys (rackOf B (B.next.vertex.trans (Fin.castLEEmb shost)))
    ((successor₀).rankPorts base₀) (((successor₀).rankPortPhase base₀ w).image ((u).before_ports ready actorMem)) earned
  rw [coindex_actor_rack (B:=B) shost (B.next.valid.host.trans_eq (sameHosts.trans allocated).symm) sameHosts] at tickets
  have income:=DateInputs.measured_funded_actors accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom run degreeAt ready mem₀ gr fee capAt history branch seen popFit popRead wireRoom oldPos
    oldWidth entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom hosts groups
    blocks capacity pitch pos readLanes readBits original safe banks oldHub oldAtom oldWire measured scan μ chosen
    saved_ snap rootPages fBits printed up one enough legal positiveQuota countFits arrivalFits
  obtain ⟨stage,cheap⟩:=DateInputs.classified_prefix («u»:=u) ready scan published
  have cut:=(u).run_to_sheets_from_actors ready (enter mem₀) actorMem stage cheap
  have tag : (inputs).tag=publicTag ctl.board k depth:=by
    change publicTag ctl.board k (GroupStage.depthBound venue.degree n f g)=_
    rw [degreeAt]
  apply captured_actor_event B accepted input.valid.host (a).ingress floor run io padDate calendar boot
    priorPath tailPath eventAt posted padded ready oldHub oldAtom oldWire entryFits calibrated safe
    used word actorMem cut.1 R read peerSize four near tag (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    pos nextHost nextChunks rawActor rankEarly inverseEarly forwardEarly peerEarly rankFits peerFits _
    paidEnd actorsEnd wireEnd hx hj gg (sameHosts.trans allocated) emitLanes capacityAt roleDegree actorDigits comp slot tickets
  obtain ⟨fund,actors,counted,inv,fw⟩:=income
  refine ⟨?_,actors,counted,inv,fw⟩
  change ∀j (p₁ : Row HH (2^(T).commonDepth) (2^e)),_=_
  intro j row_
  have value:=fund j row_
  -- The calibrated and named original banks are the same physical page.
  have address := congrArg (fun namedVenue : ResetVenue => (namedVenue.original feeStart).base) calibrated
  rw [address] at value
  exact value

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
