import OAI.Hierarchy.DescentNamedPacketRankEntry
import OAI.Hierarchy.DescentOriginalPacketRank
import OAI.Hierarchy.DescentNamedPacketDirectory
import OAI.Hierarchy.DescentNamedCalendarOriginals
import OAI.Hierarchy.DescentNamedPacketRootLimits
import OAI.Hierarchy.DescentNamedPacketRankLimits
import OAI.Hierarchy.DescentNamedRankSectors
import OAI.Hierarchy.DescentNamedRootPacketRooms
import OAI.Hierarchy.DescentNamedChartRootBank
import OAI.Hierarchy.DescentNamedOriginalSenderRoom
import OAI.Hierarchy.DescentNamedPostedStemGeometry
import OAI.Hierarchy.DescentNamedScalarLayout
import OAI.Hierarchy.DescentNamedDonorSources
import OAI.Hierarchy.DescentNamedPacketIntake
import OAI.Hierarchy.DescentResetReceiverPitch

namespace OAI
/-! # Reached rank inputs and the original signed roster after one named reset prefix -/
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
local notation "succ₀" => (a).successor
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
local notation "actorBase" => (succ₀).middle.stop base₀
local notation "early" => (succ₀).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (succ₀).front.SceneRoom early ((succ₀).issuedScene base₀ older) w)
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
local notation "priorCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal io.wire io.roster succ₀
local notation "sourceRows" => DescentResetCanvasIngress.datedLayout input HH (succ₀).funded.oldLanes
  (priorCPU).lanes (priorCPU).short (succ₀).funded.precision (priorCPU).bits
local notation "oldCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal
  ((sourceRows).tokenAt floor) io.roster succ₀
local notation "geom₀" => (a).chart start
local notation "fresh" => (geom₀).remixEnd (a).payload (a).gain (a).positive
local notation "phys₀" => DescentGLPacked.BankImage.Dated.chart (E).endAddress (geom₀).routedHosts (a).high (a).low (a).bits
local notation "savedAddress" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((phys₀).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation "digits" => S.resetInputDigits ctl.base ctl.radix age
local notation "peer₀" => PackedFlow.portAt input.placement (input.placement.numberedHeader digits input.vertex).site

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (DescentDenseHostOrder.roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "prev" => fun v=>(Z).placement.b (B.frame.host v)
local notation "U" => (succ₀).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

open DescentSortedRoster
local notation:max "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation:max "heldRoot" degreeAt:arg capAt:arg measured:arg =>
  (∃hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
        (imageOf degreeAt capAt).book measured,
    ∃x : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host (succ₀).middle.rootField,
      ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
        (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources x nBits tBits)

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
local notation "prior_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation:max "views" degreeAt:arg => fromBoard_menu (ctl:=ctl) M p drift degree payload e previous nextM base₀ prior_ degreeAt
local notation:max "menuGeometry" degreeAt:arg capAt:arg => mixed_geometry (B:=B) (oldBatch:=2^e) (batch:=M) (calendar:=cal) (paid:=capAt) (v:=succ₀)
  (front:=(views degreeAt).1) (sheets:=(views degreeAt).2) (base:=base₀)
local notation:max "datePeerSlots" degreeProof:arg =>
  (show (succ₀).front.peer.hosts=HH*(DescentDenseHostOrder.roster (Z).graph res (GroupStage.depthBound D n f g)).card from by
    change HH*(DescentDenseHostOrder.roster board k Ht).card=_
    rw [degreeProof]
    exact congrArg (HH*·) (calendar_palette B))
local notation "unitTicket" => originalBits D k n (GroupStage.depthBound D n f g) input.placement.cap
  (programCount board (GroupStage.depthBound D n f g)) g
local notation "areaDir" => (⟨(U).endAddress actorBase,HH,rows,chunks (2^(T).commonDepth) (2^e)⟩ :
  DescentResetNewActorDirectory.Layout)
local notation "pg" => ((false,.inr (⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le k) (by decide)⟩,none)) :
  DescentSixParty.Chronology.RootPage k (2^n))
local notation:max "transported" degreeAt:arg _capAt:arg => ((Receiver.IssuedDeck.mk (atlas).directions (atlas).board
  (atlas).primitive pg).reindex ((degreeAt).trans input.branch.symm) B.dimension.symm (calendar_residual B).symm)
local notation:max "actualBook" dd:arg cd:arg => (imageOf dd cd).receiver.issuedBook E (P).S (P).X (P).base (P).bank g
  (transported dd cd).peers (atlas).hostIndex (.lit input.placement.cap) f (quota S.rounds) amp (P).S.total (a).ports
  (Z).graph (Z).width C (atlas).groupDigits (atlas).batches (DescentRecordedRotorLayers.width f input.placement.cap)
  (atlas).factor (transported dd cd).primitive (transported dd cd).page
local notation:max "actualSources" dd:arg cd:arg => (imageOf dd cd).receiver.atlasSources E (P).S (P).X (P).base (P).bank g
  (transported dd cd).peers (atlas).hostIndex (.lit input.placement.cap) f (quota S.rounds) amp (P).S.total (a).ports
  (Z).graph (Z).width C (atlas).groupDigits (atlas).batches (DescentRecordedRotorLayers.width f input.placement.cap)
  (atlas).factor (transported dd cd).primitive (transported dd cd).page
private theorem same_book_image {α β : Sort _} {P₀ : α → Prop} (f₀ : (q₀ : α) → P₀ q₀ → β)
    {x₀ y₀ : α} (eqn : x₀=y₀) (a₀ : P₀ x₀) (b₀ : P₀ y₀) : f₀ x₀ a₀ = f₀ y₀ b₀ := by
  cases eqn
  rfl

open DescentSixParty.Chronology DescentPaidResidentCount.Reset DescentGroupPeerOrder DescentFallbackRankRAM
open DescentPlainTerminal.Suffix DescentPacking.PackedMatch.Local.Stage.Chooser
local notation "areaOn" dd:arg cd:arg bk:arg src:arg => (src).OperandRoom HH (2^(T).commonDepth) (2^e) w ((imageOf dd cd).receiver.headerEnd bk)
local notation "arenaOn" dd:arg cd:arg bk:arg => RootTemplates.arena ((imageOf dd cd).receiver.headerEnd bk) HH (2^(T).commonDepth) (2^e) res (Z).n input.placement.degree
local notation:max "nativePage" side₀:arg root₀:arg => (Receiver.privatePage side₀ root₀ : RootPage res (2^(Z).n))
local notation:max "pagesOn" dd:arg cd:arg bk:arg => (∀side₀ root₀ j₀, (((bk).table (nativePage side₀ root₀)).2.reads j₀).Fits w ((arenaOn dd cd bk).middle (rootIndex res (2^(Z).n) (nativePage side₀ root₀)).val))
local notation:max "packedOn" bk:arg => (∀side₀ root₀, (2^e)*max (((bk).table (nativePage side₀ root₀)).2.field*((bk).table (nativePage side₀ root₀)).1) ((bk).table (nativePage side₀ root₀)).2.outputBits ≤ w/2)

section NativeReceipt
variable (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (succ₀).funded.oldLanes (succ₀).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (succ₀).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(succ₀).funded.oldLanes) (oldWidth : (succ₀).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w)
    (oldHubRoom : HH≤ io.hubs.size) (capacity : venue.cap=cap) (pitchOld : venue.lanes=2^previous)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(succ₀).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w)
    (blocksAt : venue.k=k) (hostsAt : venue.hosts=HH) (boardRoom : h≤2^k)
    (elapsed : 0<age) (sorted : SourceSorted W input.order)
include accepted degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth entryFits low score
  live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom capacity pitchOld chosen pitch
  small word ceiling blocksAt hostsAt boardRoom elapsed sorted

set_option maxHeartbeats 2200000 in
theorem DateInputs.fromNamed_rank_controls_aux :
    ∃(μ : DescentGL.Layout (E).dim) (measured dst : Memory w),HEq μ B.frame.basis ∧
      measured (P).saved=((DescentExterior.matrixCode μ).val:Word w) ∧
      ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
        count (E).depthRows (rc).stencil book measured ∧
      ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
        ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      (pub).Exec measured dst ticks ∧ heldRoot degreeAt capAt measured ∧
      (ActorTrunkReads B input.valid.host (succ₀).front early ((succ₀).issuedScene base₀ (u).earlier) (u).sceneFits dst ∧

      ∃R : (u).MeasuredChannels (Fintype.card B.next.V), DateInputs.CaptureRoom R dst ∧ ClosedReset.Window.CapturedSelf B (u) R ∧
        (∀v₀ : B.next.V,DescentSortedRoster.present (DescentResetPeerUnionRAM.selfPeers (ClosedReset.Window.renumberPeer (datePeerSlots degreeAt) R.near))
          (rawId v₀)=(insert v₀ ((Z).emittedNear T v₀)).map rawId) ∧
        (∀v₀ : B.next.V,DescentSortedRoster.present (ClosedReset.Window.renumberPeer (datePeerSlots degreeAt) R.near)
          (rawId v₀)=((Z).emittedNear T v₀).map rawId) ∧
        Nonempty (RankSources B (b:=(succ₀).sheets.metaBits) (t:=unitTicket) (M:=(succ₀).sheets.lanes)
          (rackOf B (((Z).denseHostRank T rank).trans (Fin.castLEEmb B.next.valid.host)))
          ((succ₀).rankPorts base₀) (sheetHeader B ((succ₀).sheetsStart base₀) (u).sectors.pageBits)
          (sheetOriginal B ((succ₀).sheetsStart base₀) (u).sectors.pageBits)
          (((succ₀).rankPortPhase base₀ w).image ((u).before_ports ready dst)))):= by
  subst D
  let D := venue.degree
  have nz : 0<M:=pitch ▸ Nat.two_pow_pos e
  obtain ⟨front₀,ss₀⟩:=views (rfl:venue.degree=venue.degree)
  have front : (succ₀).front = _ := (congrArg ResetOutput.front (named_successor ..)).trans front₀
  have ss : (succ₀).sheets = _ := (congrArg ResetOutput.sheets (named_successor ..)).trans ss₀
  let dims:=mixed_geometry (B:=B) (oldBatch:=2^e) (batch:=M) (calendar:=cal) (paid:=capAt)
    («v»:=succ₀) (front:=front) (sheets:=ss) (base:=base₀)
  obtain ⟨hx,hs,hc,hp,hosts,groups,sameGroups,sameLanes,bound,newRoom⟩:=
    named_rank_sectors B p drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io
      floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom capAt rfl ready
  obtain ⟨grid,actorFit,actorSpan,chunkRoom,dirRoom,lower⟩:=
    DateInputs.fromNamed_packet_directory (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
      sceneRoom rfl blocksAt hostsAt capAt nz ready
  have since : early=(areaDir).endAddress:=congrArg DescentResetNewActorDirectory.Layout.endAddress grid
  obtain ⟨μ,measured,dst,won,saved,kept,reserved,order,panel,stencilRun,posted,whole,ct,inv,fwd,flags,
    lowDst,rootProof,stemBasis,mid,post,oldFit,oldSize,oldRead,occupied,below,depths,levels,midHub,finalHub⟩:=
    DateInputs.fromNamed_packet_entry accepted drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
      sceneRoom rfl ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth entryFits low
      score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom capacity pitchOld chosen pitch
      small word ceiling
  refine ⟨μ,measured,dst,won,saved,panel,stencilRun,posted,rootProof,?_⟩
  obtain ⟨sameBook,sameSources⟩:=fromNamed_root_image_calendar (B:=B) drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared rfl capAt gr fee
  have fit : (imageOf rfl capAt).receiver.PreparedFits (actualBook rfl capAt):=sameBook ▸ (imageOf rfl capAt).prepared
  obtain ⟨hdr,x,original⟩ : ∃hdr:DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host (imageOf rfl capAt).receiver
      (actualBook rfl capAt) measured,∃x:DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host (succ₀).middle.rootField,
      RootPacket B (imageOf rfl capAt).receiver (actualBook rfl capAt) fit measured hdr
        (actualSources rfl capAt) x nBits tBits:=by
    simpa only [←sameBook,←sameSources] using rootProof
  have rootBudget:=named_packet_root_limits B p drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w accepted gr fee branch rfl capAt degreePos small word
  have aligned : ResetOutput.ContactAligned (succ₀):=by
    rw [named_successor, pitch]
    apply ResetOutput.fromBoard_contact_aligned
  have tariffs : ∀t,t∈(succ₀).rootUnits ∨ t∈(succ₀).receiverUnits→t*(succ₀).receiver.lanes≤payload/2:=by
    intro t liveTable
    subst M
    subst e
    obtain ⟨inventoryRoot,inventoryReceiver,_,_⟩ :=
      selected_inventory G S board k tail age p f g drift degree payload previous nextM C packet
        oldLanes primitiveLanes printedBits venue io.wire io.roster floor
    apply selected_room G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue io.wire io.roster floor t _ liveTable
    unfold ResetOutput.groupWidth at small ⊢
    rw [←inventoryRoot, ←inventoryReceiver]
    exact small
  obtain ⟨earlier,later⟩:=named_packet_rank_rooms B (2^e) M cal capAt (u) front ss boardRoom dims ready nz aligned tariffs word
  have geometry:=calendar_sheet_geometry (ctl:=ctl) (oldBatch:=2^e) (batch:=M) (calendar:=cal) (I:=u) front ss
  have financial:=named_word_geometry B p drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom capAt rfl ready
  have scalar:=(named_original_scalar_layout G S board k tail age p f g drift degree payload e previous M nextM C
    packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom)
  have wiring : (u).DonorWiring:=by
    subst M
    exact named_donor_wiring G S board k tail age p f g drift degree payload e previous nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
      previousArguments initial prepared sceneRoom
  have stem:=named_posted_stem_geometry B p drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor capAt rfl
  obtain ⟨chart,addr,levelFit,range,depthRead,common,shortDepth,counted,owner,pagesFit,pagesPacked⟩:=
    DateInputs.named_root_packet_rooms (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
      venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
      rfl capAt ready chosen pitch small word ceiling score measured μ reserved order panel popFit
  have source:=fromNamed_calendar_originals (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io
    floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom rfl capAt
  have dim : (E).dim=(Z).k:=(sh).dimension.symm.trans B.keyWidth.symm
  let originalMap:=cast (congrArg DescentGL.Layout dim) μ
  have mapWon : HEq originalMap B.frame.basis:=(cast_heq _ _).trans won
  let rc₁:=(imageOf rfl capAt).receiver
  let fromHere:=EarlierBanks.castTo input.branch (calendar_residual B) capAt B.dimension
    (EarlierBanks.fromRoot rc₁ (actualBook rfl capAt) (actualSources rfl capAt) (atlas).hostIndex io.hubs areaDir scene)
  have beforeRoots:=fromNamed_root_state (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared rfl capAt measured
  let originalBanks:=EarlierBanks.castTo input.branch (calendar_residual B) capAt B.dimension
    (EarlierBanks.fromRoot rc₁ (imageOf rfl capAt).book (imageOf rfl capAt).sources (atlas).hostIndex io.hubs dir scene)
  have banksEq : originalBanks=fromHere:= by
    exact congrArg (EarlierBanks.castTo input.branch (calendar_residual B) capAt B.dimension)
      (congrArg₂ (fun pair₀ layout₀=>EarlierBanks.fromRoot rc₁ pair₀.1 pair₀.2
        (atlas).hostIndex io.hubs layout₀ scene) (congrArg₂ Prod.mk sameBook sameSources) grid)
  let pricedField := ResetMiddle.fieldWidth venue.degree cap n k Ht
  let pricedBits := (CandidateSheets.fromBoard S board k tail age venue.degree f g cap M).metaBits
  let pricedFront := setupFront S board k tail age venue.degree f g (2^e) M pricedField pricedBits C packet cal
  let pricedOriginal (addr : ℕ) := calendarOriginals S board k tail age venue.degree f g (2^e) M
      pricedField pricedBits C packet cal addr fromHere
  have pricedFrontEq : (succ₀).front = pricedFront := front
  have pricedBack : HEq (u).earlier (pricedOriginal early) :=
    source.trans (heq_of_eq (congrArg (fun banks₀=>calendarOriginals S board k tail age venue.degree f g (2^e) M
      pricedField pricedBits C packet cal early banks₀) banksEq))
  have pricedStable : HEq (u).earlier (pricedOriginal (areaDir).endAddress) :=
    pricedBack.trans (by rw [since])
  have pricedSafe := original_probe_room pricedFrontEq since (u).earlier (pricedOriginal (areaDir).endAddress) pricedStable
    (congrArg DescentResetNewActorDirectory.Layout.flags grid) (congrArg DescentResetNewActorDirectory.Layout.count grid)
    (congrArg DescentResetNewActorDirectory.Layout.inverse grid) sceneRoom
  obtain ⟨idFit,idRoom,idWords,rootEnd,hubFit,hubSpan,account⟩:=
    DateInputs.fromNamed_packet_intake (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom rfl capAt ready mem measured seen μ order
  have pricedKey : pricedFront.oldKeys (areaDir).endAddress < 2^w := by
    exact (congrArg₂ CandidateFront.oldKeys pricedFrontEq since) ▸ account
  have rootArea:=fromNamed_root_area (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom rfl capAt ready chosen pitch small word ceiling
  have rootStop : rc₁.preparedEnd (imageOf rfl capAt).book=actorBase:=by
    have eqn : rc₁.preparedEnd (imageOf rfl capAt).book=(rc).preparedEnd book:=by
      unfold rc₁ fromNamed_root_image
      apply Receiver.IndexedRoots.preparedEnd_reindex
    rw [eqn]
    exact named_root_prepared_end G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  have tree : ∀s t,(u).earlier.pages s t=rc₁.privatePageBank (actualBook rfl capAt) s (chartTicket (date:=a) (floor:=start) B (2^e) M cal dims t):=by
    intro s t
    rw [←sameBook]
    apply fromNamed_chart_root_bank
  have retained : ∀j,j<rc₁.preparedEnd (actualBook rfl capAt)→mid j=rc₁.preparedImage (actualBook rfl capAt) fit measured j :=by
    intro j hj
    have ends := congrArg rc₁.preparedEnd sameBook
    have images := same_book_image (fun q fit₀=>rc₁.preparedImage q fit₀ measured) sameBook
      (imageOf rfl capAt).prepared fit
    exact (below j (hj.trans_eq (ends.symm.trans rootStop))).trans
      (congrFun (beforeRoots.2.2.2.2.2.symm.trans images) j)
  have stopEq : (succ₀).trunkEnd base₀ = pricedFront.trunkEnd (areaDir).endAddress :=
    congrArg₂ CandidateFront.trunkEnd pricedFrontEq since
  let pricedDonor := peerDonorShape B HH (2^e) pricedField (Nat.clog 2 (venue.degree+2)) (Nat.clog 2 (venue.degree+3))
  let pricedOrigin (addr : ℕ) := (peerLayout B (pricedFront.oldKeys addr) HH (2^e)
      pricedFront.privateBits (pricedFront.stemField+2) pricedFront.peer.bits).endAddress
  let pricedContact (addr : ℕ) := contactLayout B (pricedDonor.endAddress (pricedOrigin addr))
      HH (2^e) pricedField pricedFront.peer.bits
  let pricedAddress (addr : ℕ) := (pricedContact addr).endAddress
  let pricedGood := contactOutputs B HH (2^e) pricedField (Nat.clog 2 (venue.degree+2)) (Nat.clog 2 (venue.degree+3))
      (S.groupCount (age+1)) (2^k) M pricedFront.peer.bits pricedBits
  have pricedRight : pricedAddress (areaDir).endAddress ≤ pricedFront.trunkEnd (areaDir).endAddress := by
    have h : pricedAddress early ≤ (succ₀).trunkEnd base₀ := earlier.right
    exact (congrArg pricedAddress since) ▸ stopEq ▸ h
  have pricedRemote : pricedGood.marker (pricedFront.trunkEnd (areaDir).endAddress) +
      HH * chunks (2^(T).commonDepth) (2^e) < 2^w := by
    have h : pricedGood.marker ((succ₀).trunkEnd base₀) + HH * chunks (2^(T).commonDepth) (2^e) < 2^w :=
      earlier.remote
    exact stopEq ▸ h
  have pricedDateEnd : pricedGood.endAddress (pricedFront.trunkEnd (areaDir).endAddress) < 2^w := by
    have h : pricedGood.endAddress ((succ₀).trunkEnd base₀) < 2^w := earlier.dateEnd
    exact stopEq ▸ h
  have pricedTrunkRoom : pricedFront.trunkEnd (areaDir).endAddress < 2^w := stopEq ▸ later.trunkRoom
  have pricedPriorPaid := named_sender_room B (2^e) M pricedField pricedBits cal capAt (succ₀)
    base₀ fromHere pricedFrontEq dims.contactDeck (u).earlier pricedBack sceneRoom
  let donorSpaceAt (addr : ℕ) := pricedDonor.Space (pricedOrigin addr)
      (DescentContactDonorFront.Shape.move (canonical_donor B (2^e) M pricedField pricedBits cal capAt) fromHere.donor) w
  have pricedDonorRoom : donorSpaceAt (areaDir).endAddress :=
    Eq.mp (congrArg donorSpaceAt since) pricedPriorPaid.1
  let senderPacked (addr : ℕ) := (pricedDonor.sender (pricedOrigin addr)).Packed w
  have pricedPacked : senderPacked (areaDir).endAddress := Eq.mp (congrArg senderPacked since) earlier.packedDonor
  let endFits (addr : ℕ) := pricedAddress addr < 2^w
  have pricedEndRoom : endFits (areaDir).endAddress := Eq.mp (congrArg endFits since) earlier.endRoom
  let boardFits (addr : ℕ) := (2^e)*max (pricedField*(pricedContact addr).oldFields) (pricedContact addr).viewBits ≤ w/2
  have pricedBoard : boardFits (areaDir).endAddress := Eq.mp (congrArg boardFits since) earlier.boardWidth
  let programFits (addr : ℕ) := DescentResetPeerUnionRAM.Program.endAddress (pricedAddress addr) HH rows
      input.placement.degree (ClosedReset.Window.peerEvidenceRows B) pricedFront.peer.bits (2^e) < 2^w
  have pricedProgramRoom : programFits (areaDir).endAddress := Eq.mp (congrArg programFits since) earlier.room
  have sameMid := same_book_image (fun q (hq : rc₁.PreparedFits q) => rc₁.preparedMid q hq measured)
    sameBook (imageOf rfl capAt).prepared fit
  have headerEq := congrArg rc₁.headerEnd sameBook
  have endEq := congrArg rc₁.preparedEnd sameBook
  have pricedArea : areaOn rfl capAt (actualBook rfl capAt) (actualSources rfl capAt) := by
    rw [←sameBook, ←sameSources]
    exact rootArea
  have pricedPages : pagesOn rfl capAt (actualBook rfl capAt) := by
    rw [←sameBook]
    exact pagesFit
  have pricedPagesPacked : packedOn (actualBook rfl capAt) := by
    rw [←sameBook]
    exact pagesPacked
  have outEq : dst = (areaDir).result scene mid :=
    post.trans (congrArg (fun deck₀ : DescentResetNewActorDirectory.Layout => deck₀.result scene mid) grid)
  have packetProofs := original_packet_rank_controls_aux
    (bw:=w) (t:=tBits) (nbits:=nBits)
    (B:=B)
    (M:=2^e)
    (nextM:=M)
    (calendar:=cal)
    (paid:=capAt)
    («rc»:=rc₁)
    («E»:=E)
    (stencil:=(P).S)
    (source:=(P).X)
    (base:=(P).base)
    (split:=(P).bank)
    (hubWidth:=g)
    (ports:=(transported rfl capAt).peers)
    (oldId:=(atlas).hostIndex)
    (oldHub:=io.hubs)
    (fee:=quota S.rounds)
    (total:=(P).S.total)
    (portPitch:=(a).ports)
    (groupDigits:=(atlas).groupDigits)
    (batches:=(atlas).batches)
    (factor:=(atlas).factor)
    (primitive:=(transported rfl capAt).primitive)
    (page:=(transported rfl capAt).page)
    (space:=fit)
    (mem:=measured)
    (directory:=(U).endAddress actorBase)
    (actorBank:=scene)
    (before:=mid)
    (safe:=pricedSafe)
    (x:=x)
    (levels:=ClosedReset.Recorded.oldDepth B)
    (unit:=by
      rw [B.unit, ← input.grain]
      exact Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right rootBudget.active))
    (I:=u)
    (recorded:=accepted)
    (hdr:=hdr)
    (μ:=originalMap)
    (won:=mapWon)
    («packet»:=original)
  have sizeProofs := packetProofs
    (level:=rootBudget.level)
    (one:=rootBudget.one)
    (mass:=rootBudget.mass)
    (codes:=rootBudget.codes)
    (active:=rootBudget.active)
    (quotaPos:=rootBudget.quotaPos)
    (degreePos:=rootBudget.degreePos)
    (depths:=ClosedReset.Recorded.oldDepth_at B)
    (precision:=rootBudget.precision)
    (depthFit:=rootBudget.depthFit)
    (capFit:=rootBudget.capFit)
    (elapsed:=elapsed)
    (sorted:=sorted)
    (baseRoom:=rootBudget.baseRoom)
    (dimension:=rootBudget.dimension)
    (socketRoom:=rootBudget.socketRoom)
    (heightRoom:=rootBudget.heightRoom)
    (portRoom:=rootBudget.portRoom)
    (lanes:=Nat.two_pow_pos _)
    (physicalHosts:=rfl)
    (extent:=hostBits)
  have rootInputProofs := sizeProofs
    (counted:=fun q₀ => (congrArg (fun m₀ => (P).X.count.eval m₀ ((row HH (2^(T).commonDepth) (2^e) q₀).val : Word w)) sameMid).symm.trans (counted q₀))
    (owner:=fun q₀ => (congrArg (fun m₀ => (Expr.lookup (atlas).hostIndex .row).eval m₀ ((row HH (2^(T).commonDepth) (2^e) q₀).val : Word w)) sameMid).symm.trans (owner q₀))
    (chart:=(congrArg ((P).S.header (P).base).chart.Resident sameMid).mp chart)
    (addresses:=(congrArg (((P).S.header (P).base).depth.Fits w) headerEq).mp addr)
    (priorDepths:=(congrArg ((P).X.levels.Fits w) headerEq).mp levelFit)
    (range:=range)
    (observedDepth:=fun v₀ hv => (congrFun sameMid _).symm.trans (depthRead v₀ hv))
    (common:=common)
    (shortDepth:=shortDepth)
    (low:=rootBudget.low)
    (rankRoom:=rootBudget.rankRoom)
    (area:=pricedArea)
    (rootsFit:=pricedPages)
    (rootsPacked:=pricedPagesPacked)
  have actorProofs := rootInputProofs
    (rootEnd:=endEq.symm.trans_le rootEnd)
    (kept:=retained)
    (actorFit:=actorFit)
    (actorSpan:=actorSpan)
    (occupied:=occupied)
    (chunkRoom:=chunkRoom)
    (keyRoom:=pricedKey)
    (idFit:=idFit)
    (idRoom:=idRoom)
    (hostWords:=idWords)
    (donorRoom:=pricedDonorRoom)
    (romRoom:=Eq.mp (congrArg (fun addr => pricedOrigin addr < 2^w) since) pricedPriorPaid.2)
  have roomProofs := actorProofs
    (endRoom:=pricedEndRoom)
    (packedMarker:=earlier.packedMarker)
    (wordPositive:=earlier.wordPositive)
    (packedDonor:=pricedPacked)
    (boardWidth:=pricedBoard)
    (shapeWidth:=earlier.shapeWidth)
    (markerWidth:=earlier.markerWidth)
    (room:=pricedProgramRoom)
    (maxHost:=boardRoom)
    («cal»:=dims)
    (ok:=ready)
    (grid:=grid)
    (front:=pricedFrontEq)
    (back:=pricedBack)
    (ss:=ss)
    (bound:=bound)
    (newHosts:=newRoom)
    (dirRoom:=dirRoom)
    (right:=pricedRight)
    (remote:=pricedRemote)
    (items:=earlier.items)
  have siteProofs := roomProofs
    (hubFit:=hubFit)
    (hubSpan:=hubSpan)
    (hubRead:=midHub)
    (width:=later.width)
    (trunkRoom:=pricedTrunkRoom)
    (degreeWord:=later.degreeWord)
    (capWord:=later.capWord)
    (alphabet:=later.alphabet)
    (wordAlphabet:=later.wordAlphabet)
    (geo:=geometry)
    (hx:=hx)
    (hs:=hs)
    (hc:=hc)
    (hp:=hp)
    (oldFits:=⟨oldFit.1,oldFit.2.1,oldFit.2.2.trans lower⟩)
    (oldSize:=oldSize)
    (oldRead:=oldRead)
    (pageAddr:=tree)
    (dateEnd:=pricedDateEnd)
  have all := siteProofs
    (joints:=earlier.joints)
    (lanePositive:=later.lanePositive)
    (rankFit:=later.rankFit)
    (maskFit:=later.maskFit)
    (shape:=financial)
    (scalar:=scalar)
    (wire:=wiring)
    (stem:=stem)
    (basis:=by rw [←outEq]; exact stemBasis)
    (hosts:=hosts)
    (groups:=groups)
    (sameGroups:=sameGroups)
    (sameLanes:=sameLanes)
  rw [outEq]
  exact all

theorem DateInputs.fromNamed_rank_controls :
    ∃(μ : DescentGL.Layout (E).dim) (measured dst : Memory w),HEq μ B.frame.basis ∧
      measured (P).saved=((DescentExterior.matrixCode μ).val:Word w) ∧
      ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
        count (E).depthRows (rc).stencil book measured ∧
      ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
        ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      (pub).Exec measured dst ticks ∧ heldRoot degreeAt capAt measured ∧
      (ActorTrunkReads B input.valid.host (succ₀).front early ((succ₀).issuedScene base₀ (u).earlier) (u).sceneFits dst ∧

      ∃R : (u).MeasuredChannels (Fintype.card B.next.V), DateInputs.CaptureRoom R dst ∧
        (∀v₀ : B.next.V,DescentSortedRoster.present (DescentResetPeerUnionRAM.selfPeers (ClosedReset.Window.renumberPeer (datePeerSlots degreeAt) R.near))
          (rawId v₀)=(insert v₀ ((Z).emittedNear T v₀)).map rawId) ∧
        (∀v₀ : B.next.V,DescentSortedRoster.present (ClosedReset.Window.renumberPeer (datePeerSlots degreeAt) R.near)
          (rawId v₀)=((Z).emittedNear T v₀).map rawId) ∧
        Nonempty (RankSources B (b:=(succ₀).sheets.metaBits) (t:=unitTicket) (M:=(succ₀).sheets.lanes)
          (rackOf B (((Z).denseHostRank T rank).trans (Fin.castLEEmb B.next.valid.host)))
          ((succ₀).rankPorts base₀) (sheetHeader B ((succ₀).sheetsStart base₀) (u).sectors.pageBits)
          (sheetOriginal B ((succ₀).sheetsStart base₀) (u).sectors.pageBits)
          (((succ₀).rankPortPhase base₀ w).image ((u).before_ports ready dst)))):=by
  obtain ⟨μ,measured,dst,won,savedValue,panel,scanned,posted,rootProof,trunk,R,seen,_,four,three,ranks⟩:=
    DateInputs.fromNamed_rank_controls_aux accepted drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth
      entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom capacity
      pitchOld chosen pitch small word ceiling blocksAt hostsAt boardRoom elapsed sorted
  exact ⟨μ,measured,dst,won,savedValue,panel,scanned,posted,rootProof,trunk,R,seen,four,three,ranks⟩

theorem DateInputs.fromNamed_rank_sources :
    ∃(μ : DescentGL.Layout (E).dim) (measured dst : Memory w),HEq μ B.frame.basis ∧
      measured (P).saved=((DescentExterior.matrixCode μ).val:Word w) ∧
      ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
        count (E).depthRows (rc).stencil book measured ∧
      ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
        ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      (pub).Exec measured dst ticks ∧ heldRoot degreeAt capAt measured ∧
      ∃R : (u).MeasuredChannels (Fintype.card B.next.V), DateInputs.CaptureRoom R dst ∧
        (∀v₀ : B.next.V,DescentSortedRoster.present (DescentResetPeerUnionRAM.selfPeers (ClosedReset.Window.renumberPeer (datePeerSlots degreeAt) R.near))
          (rawId v₀)=(insert v₀ ((Z).emittedNear T v₀)).map rawId) ∧
        (∀v₀ : B.next.V,DescentSortedRoster.present (ClosedReset.Window.renumberPeer (datePeerSlots degreeAt) R.near)
          (rawId v₀)=((Z).emittedNear T v₀).map rawId) ∧
        Nonempty (RankSources B (b:=(succ₀).sheets.metaBits) (t:=unitTicket) (M:=(succ₀).sheets.lanes)
          (rackOf B (((Z).denseHostRank T rank).trans (Fin.castLEEmb B.next.valid.host)))
          ((succ₀).rankPorts base₀) (sheetHeader B ((succ₀).sheetsStart base₀) (u).sectors.pageBits)
          (sheetOriginal B ((succ₀).sheetsStart base₀) (u).sectors.pageBits)
          (((succ₀).rankPortPhase base₀ w).image ((u).before_ports ready dst))) :=by
  obtain ⟨μ,measured,dst,won,savedValue,panel,scanned,posted,rootProof,_,received⟩:=
    DateInputs.fromNamed_rank_controls accepted drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth
      entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom capacity
      pitchOld chosen pitch small word ceiling blocksAt hostsAt boardRoom elapsed sorted
  exact ⟨μ,measured,dst,won,savedValue,panel,scanned,posted,rootProof,received⟩
end NativeReceipt

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
