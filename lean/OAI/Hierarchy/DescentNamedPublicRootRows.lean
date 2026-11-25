import OAI.Hierarchy.DescentNamedPublicValueRegisters
import OAI.Hierarchy.DescentNamedPublicPackedInputs
import OAI.Hierarchy.DescentNamedPacketParents
import OAI.Hierarchy.DescentPreparedPairPackedRows

namespace OAI
/-! # The five public operand arrays on the actual named reset -/
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
section
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w}
local notation "P₀" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "root" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "actorFloor" => (v).middle.stop b
local notation "A₀" => (v).actor
local notation "ds" => (A₀).directory actorFloor
local notation "scene" => (A₀).scene actorFloor
local notation "stencil" => a.throughStencil u.shape floor u.count u.hub u.g u.Y u.src u.sourceRows u.oldDegree w
local notation "scanTime" => a.throughStencilTicks u.shape floor u.count u.hub u.g u.Y u.sourceRows u.oldDegree w
local notation "publication" => (((root).preparedRoots u.book u.bookFits).seq ((A₀).classifier u.actor actorFloor w)).seq ((ds).program w scene)
local notation "ticks" => ((root).preparedTicks u.book u.bookFits+(A₀).classifierTime u.actor actorFloor w)+(ds).ticks scene

private theorem packetSegments {w : ℕ} (A B C D : Procedure w)
    {memA memB memC memD memE out : Memory w} {i j k l : ℕ}
    (scan : A.Exec memA memB i) (rootRun : B.Exec memB memC j) (classification : C.Exec memC memD k)
    (write : D.Exec memD memE l) (published : ((B.seq C).seq D).Exec memB out ((j+k)+l))
    : (A.seq B).Exec memA memC (i+j) ∧ (C.seq D).Exec memC out (k+l) := by
  have same := exec_unique ((B.seq C).seq D) memB memE out
    (@Procedure.Exec.then w (B.seq C) D memB memD memE (j+k) l
      (@Procedure.Exec.then w B C memB memC memD j k @rootRun @classification) @write) @published
  subst out
  exact ⟨@Procedure.Exec.then w A B memA memB memC i j @scan @rootRun,
    @Procedure.Exec.then w C D memC memD memE k l @classification @write⟩

private theorem publicRootExecutions (ready : u.Ready) {initial measured actors : Memory w}
    (scanned : (stencil).Exec initial measured scanTime)
    (published : (publication).Exec measured actors ticks) :
    let head:=a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
    let time:=a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
    let body:=(A₀).actorBody u.actor actorFloor w
    head.Exec initial ((root).preparedImage u.book u.bookFits measured) time ∧
      body.Exec ((root).preparedImage u.book u.bookFits measured) actors ((A₀).actorTicks u.actor actorFloor w) := by
  dsimp only
  obtain ⟨rootExec,_,_⟩:=(root).prepared_any u.book u.bookFits measured
  obtain ⟨intermediate,actual,scan,issue,_,_⟩:=(A₀).dated_parts u.actor actorFloor ((root).preparedImage u.book u.bookFits measured) ready.actor
  exact @packetSegments w stencil ((root).preparedRoots u.book u.bookFits)
    ((A₀).classifier u.actor actorFloor w) ((ds).program w scene)
    initial measured ((root).preparedImage u.book u.bookFits measured) intermediate actual actors
    scanTime ((root).preparedTicks u.book u.bookFits) ((A₀).classifierTime u.actor actorFloor w)
    ((ds).ticks scene) @scanned @rootExec @scan @issue @published

end

private theorem publicPacketRoof (a : PhysicalReset) (start w : ℕ)
    (ceiling : a.endAddress start < 2^w) :
    let v := a.successor
    let base := a.rebased start
    let last := v.operandFloor base
    v.setup.packets.endAddress (v.setup.placed last) < 2^w := by
  let v := a.successor
  let base := a.rebased start
  let C := v.setup
  let last := v.operandFloor base
  have packet : C.packetEnd last ≤ C.publicEnd last := Nat.le_add_right ..
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈⟩ := C.order last
  obtain ⟨b₁,b₂⟩ := v.operand_order base
  have kept : C.endAddress last ≤ v.operandStart base := v.keep_before base
  have scalar : v.scalarEnd base ≤ v.finalEnd base := v.final_ge base
  calc
    C.packetEnd last ≤ C.endAddress last :=
      (((((((packet.trans a₁).trans a₂).trans a₃).trans a₄).trans a₅).trans a₆).trans a₇).trans a₈
    _ ≤ v.finalEnd base := (((kept.trans b₁).trans b₂).trans scalar)
    _ ≤ a.endAddress start := date_operand_end a start
    _ < 2^w := ceiling

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
local notation "savedBase" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((phys₀).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation "reachedDigits" => S.resetInputDigits ctl.base ctl.radix age
local notation "peer₀" => PackedFlow.portAt input.placement (input.placement.numberedHeader reachedDigits input.vertex).site

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
local notation "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "heldRoot" degreeAt:arg capAt:arg measured:arg =>
  (∃hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
        (imageOf degreeAt capAt).book measured,
    ∃x : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host (succ₀).middle.rootField,
      ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
        (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources x nBits tBits)

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "height₁" => S.hostSize (age+1)
local notation "group₁" => S.groupCount (age+1)
local notation "qbits" => (succ₀).setup.rotorBits
local notation "control" => (succ₀).controlRegisters
local notation "first_" => (succ₀).controlFloor base₀
local notation "last_" => (succ₀).operandFloor base₀
local notation "prior_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "occ" x:arg => fun hostIndex groupIndex=>actualBit B B.next.valid.host hostIndex groupIndex x
local notation "scaled" => (⟨quantityDims B 1 HH height₁ (2^e) M,qbits⟩ : DescentResetControlRegisters.Chart)
local notation "levelAt_" v:arg => (Z).placement.b (DescentDenseHostOrder.position (Z).graph (v).val)

local notation "C₀" => (succ₀).setup
local notation "shelf_" => (succ₀).sheets
local notation "stage_" x:arg => (control).live first_ (x:DescentColonies.Block k).val
local notation "regs_" x:arg => (control).ports first_ ((a).c/2) (x:DescentColonies.Block k).val ((U).directory actorBase).inverse
  ((U).depths actorBase) ((U).levels actorBase)
local notation "deck_" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (stage_ x) (regs_ x)
local notation "head_" => (C₀).placement.newHosts
local notation "gang_" => (C₀).placement.groups
local notation "rows_" x:arg => (b₀:Bool)→Fin ((deck_ x).packets.stage 0 b₀).fields→Fin (deck_ x).packets.blocks→
  Fin head_→Fin gang_→Cell ((deck_ x).casts.width 0)
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
set_option hygiene true
set_option maxHeartbeats 1300000
set_option maxRecDepth 6144

/-- The original native menu, both root packets and their sources at a fixed actor memory. -/
abbrev DateInputs.OriginalPublicRowsAt (μ : DescentGL.Layout (E).dim) (measured dst : Memory w) : Prop :=
  HEq μ B.frame.basis ∧
      ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
        ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      (pub).Exec measured dst ticks ∧ heldRoot degreeAt capAt measured ∧
      ∃R : (u).MeasuredChannels (Fintype.card B.next.V),DateInputs.CaptureRoom R dst ∧
      ClosedReset.Window.CapturedSelf B (u) R ∧
      ∃(hRaw : HH=(C₀).placement.oldHosts) (sRaw : rows=(C₀).placement.shapes)
       (xCount : 2^k=(C₀).placement.blocks),∀x : DescentColonies.Block k,
      ∃(menu : (deck_ x).Values head_ gang_) (digits : (deck_ x).casts.bits=(C₀).fallbackBits),
        (u).PublicValuesRead ready dst (x.cast xCount) digits
          (fun j=>((Z).rawAtIndex T rank j).cast (congrArg₂ Nat.mul hRaw sRaw)) menu ∧
        (∀h₀ g₀,(menu.active h₀ g₀).val=((scaled).enabled (occ x) (fun _=>1) h₀ g₀).val) ∧
        (∀j h₀ g₀,(menu.register j h₀ g₀).val=((scaled).enabled (occ x)
          (controlScalar B input.valid.host B.next.valid.host j) h₀ g₀).val) ∧
        ∃packets : rows_ x,menu=(u).issuedPublicValues (x.cast xCount) R B.frame.basis rfl rfl rfl rfl rfl rfl
          menu.active menu.register packets ∧
        (∀f₀ j z₀,menu.packet f₀ j z₀=packets f₀ j z₀) ∧
        (∀f₀ j z₀,let ptr:=(deck_ x).packets.src (deck_ x).packetBase f₀ j z₀
          ptr.Fits w (deck_ x).castBase ∧ Source ptr (packets f₀ j z₀) (deck_ x).casts.lanes
            ((deck_ x).packets.image (deck_ x).packetBase ((u).beforePacketImage ready dst))) ∧
        ∃(hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
              (imageOf degreeAt capAt).book measured)
          (xs : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host (succ₀).middle.rootField),
          ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
            (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources xs nBits tBits ∧
          let O:=(C₀).packets
          ∃(groupAt : O.groups*O.blocks=2^(T).commonDepth)
            (orig : (f₀:Bool)→Fin O.actors→Fin (O.groups*O.blocks)→Cell (O.oldBits*(O.stage 0 f₀).fields)),
            (∀f₀,Source (O.original f₀) (orig f₀) O.beforeLanes
              ((rc).preparedImage (u).book (u).bookFits measured)) ∧
            (∀r j,(orig false r j).val=(DescentPaidResidentCount.Reset.savedInput B input.valid.host
              (DescentPaidResidentCount.Reset.root_snapshot B input.valid.host (imageOf degreeAt capAt).receiver
                (imageOf degreeAt capAt).book (imageOf degreeAt capAt).prepared measured hdr xs) r (j.cast groupAt)).val) ∧
            (∀r j,(orig true r j).val=(DescentSIMDLookup.encode (u).roots.field
                (DescentRotorWindowArchive.count input.placement.degree (2^((Z).k-(T).commonDepth)) input.placement.cap)
                (ClosedReset.Window.calendar_sender_matrix B (2^e) (u).roots.field (imageOf degreeAt capAt).receiver
                  (imageOf degreeAt capAt).book (imageOf degreeAt capAt).prepared measured hdr xs r (j.cast groupAt))).val) ∧
            ∀positive : 0<HH,∀f₀ j z₀ h₀ g₀,(packets f₀ j z₀ h₀ g₀).val=
              ((DescentSIMDLookup.encode O.oldBits (O.stage 0 f₀).fields).symm
                (orig f₀ ((Z).packetOwner T rank positive h₀) (finProdFinEquiv (g₀,z₀))) j).val


include accepted degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth entryFits low score
  live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom capacity pitchOld chosen pitch
  small word ceiling blocksAt hostsAt boardRoom elapsed sorted

theorem DateInputs.fromNamed_public_origins_at (run : (u).FinalInputs) (positive : 0<HH) :
    ∃(μ : DescentGL.Layout (E).dim) (measured dst : Memory w),DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
      previousArguments initial prepared sceneRoom degreeAt ready mem capAt μ measured dst :=by
  obtain ⟨μ,measured,dst,won,_,_,_,_,_,scan,posted,_,_,_,_,flags,_⟩:=
    DateInputs.fromNamed_packet_entry (B:=B) accepted drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
      sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth entryFits low
      score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom capacity pitchOld chosen pitch
      small word ceiling
  obtain ⟨_,previous_,actors_,_,scanned,published,root_,R,captured,selfWord,hRaw,sRaw,xCount,pages⟩:=
    DateInputs.fromNamed_public_values_and_self accepted drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
      sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth entryFits low
      score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom capacity pitchOld chosen pitch
      small word ceiling blocksAt hostsAt boardRoom elapsed sorted
  have appearance : previous_=measured:=ProtocolRAM.exec_unique _ _ _ _ scanned scan
  subst previous_
  have installed : actors_=dst:=ProtocolRAM.exec_unique _ _ _ _ published posted
  subst actors_
  refine ⟨μ,measured,dst,won,scan,posted,root_,R,captured,selfWord,hRaw,sRaw,xCount,?_⟩
  obtain ⟨hdr,xs,stored⟩:=root_
  have height : GroupStage.depthBound D n f g + 2 < w := by
    have packing := fromNamed_matrix_packing G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count chosen pitch small word ceiling capacity
    have positiveCount : 0 < DescentRotorWindowArchive.count venue.degree (2^k) venue.cap := by
      unfold DescentRotorWindowArchive.count
      positivity
    let registerWidth := (succ₀).middle.rootField
    have shelf : registerWidth ≤ registerWidth * DescentRotorWindowArchive.count venue.degree (2^k) venue.cap :=
      Nat.le_mul_of_pos_right _ positiveCount
    have room : registerWidth ≤ w / 2 :=
      shelf.trans ((Nat.le_max_left _ _).trans ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos e)).trans packing.1))
    have depth : Ht + 2 ≤ registerWidth := packing.2.2
    rw [←degreeAt]
    omega
  obtain ⟨groupAt,words_,physical,fallback_,matrix_⟩:=DateInputs.fromNamed_public_packed_values (B:=B) drift degree payload e previous
    M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared sceneRoom degreeAt capAt run measured hdr xs stored ready
    chosen pitch small word ceiling height capacity gr fee
  have ptrs:=DateInputs.named_packet_registers G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom run ctl.base ctl.radix B.age
  have ptrRead:=fun f₀=>(And.intro (ptrs.2.2 f₀) (physical f₀))
  have nextLanes : 0<M:=pitch ▸ Nat.two_pow_pos _
  have parent_:=DateInputs.fromNamed_packet_parents (B:=B) drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared sceneRoom degreeAt blocksAt hostsAt capAt nextLanes ready dst flags positive
  let afterRoots:=(rc).preparedImage (u).book (u).bookFits measured
  obtain ⟨headRun,actorRun⟩ := publicRootExecutions («u»:=u) ready scan posted
  have roof : (C₀).packets.endAddress ((C₀).placed last_)<2^w := publicPacketRoof (a) start w ceiling
  have dated := named_successor G S ctl.board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io.wire io.roster floor
  have parentAt : (succ₀).setup.packets.parent = ((succ₀).front.parent early).base := by
    rw [dated]
    rfl
  have paddingAt : (succ₀).setup.packets.receivers = (succ₀).front.newHosts := by
    rw [dated]
    rfl
  have keptRoom : (C₀).packets.parent + (C₀).packets.receivers ≤ (succ₀).trunkEnd base₀ := by
    rw [parentAt, paddingAt]
    exact ((u).parent_room ready).1
  intro x
  have oldPitch : 0<(C₀).packets.beforeLanes:=by change 0<2^e;exact Nat.two_pow_pos _
  have width_ : (deck_ x).casts.width 0=(C₀).packets.oldBits:=by rfl
  have lane_ : (deck_ x).casts.lanes=(C₀).packets.afterLanes:=by rfl
  obtain ⟨packets,reads,values⟩:=@DateInputs.public_packed_rows (a) start w (u) ready (stage_ x) (regs_ x)
    words_ ((Z).packetOwner T rank positive) ((entry₀).image mem) afterRoots dst @headRun
    @actorRun ptrRead parent_ keptRoom oldPitch roof width_ lane_
  obtain ⟨menu,digits,read,identity,stored_,active_,registers_⟩:=pages x packets reads
  exact ⟨menu,digits,read,active_,registers_,packets,identity,stored_,reads,
    hdr,xs,stored,groupAt,words_,physical,fallback_,matrix_,fun _=>values⟩

theorem DateInputs.fromNamed_public_operand_origins (run : (u).FinalInputs) (positive : 0<HH) :
    ∃(μ : DescentGL.Layout (E).dim) (measured dst : Memory w),HEq μ B.frame.basis ∧
      ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
        ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      (pub).Exec measured dst ticks ∧ heldRoot degreeAt capAt measured ∧
      ∃R : (u).MeasuredChannels (Fintype.card B.next.V),DateInputs.CaptureRoom R dst ∧
      ClosedReset.Window.CapturedSelf B (u) R ∧
      ∃(hRaw : HH=(C₀).placement.oldHosts) (sRaw : rows=(C₀).placement.shapes)
       (xCount : 2^k=(C₀).placement.blocks),∀x : DescentColonies.Block k,
      ∃(menu : (deck_ x).Values head_ gang_) (digits : (deck_ x).casts.bits=(C₀).fallbackBits),
        (u).PublicValuesRead ready dst (x.cast xCount) digits
          (fun j=>((Z).rawAtIndex T rank j).cast (congrArg₂ Nat.mul hRaw sRaw)) menu ∧
        (∀h₀ g₀,(menu.active h₀ g₀).val=((scaled).enabled (occ x) (fun _=>1) h₀ g₀).val) ∧
        (∀j h₀ g₀,(menu.register j h₀ g₀).val=((scaled).enabled (occ x)
          (controlScalar B input.valid.host B.next.valid.host j) h₀ g₀).val) ∧
        ∃packets : rows_ x,menu=(u).issuedPublicValues (x.cast xCount) R B.frame.basis rfl rfl rfl rfl rfl rfl
          menu.active menu.register packets ∧
        (∀f₀ j z₀,menu.packet f₀ j z₀=packets f₀ j z₀) ∧
        (∀f₀ j z₀,let ptr:=(deck_ x).packets.src (deck_ x).packetBase f₀ j z₀
          ptr.Fits w (deck_ x).castBase ∧ Source ptr (packets f₀ j z₀) (deck_ x).casts.lanes
            ((deck_ x).packets.image (deck_ x).packetBase ((u).beforePacketImage ready dst))) ∧
        ∃(hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
              (imageOf degreeAt capAt).book measured)
          (xs : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host (succ₀).middle.rootField),
          ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
            (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources xs nBits tBits ∧
          let O:=(C₀).packets
          ∃(groupAt : O.groups*O.blocks=2^(T).commonDepth)
            (orig : (f₀:Bool)→Fin O.actors→Fin (O.groups*O.blocks)→Cell (O.oldBits*(O.stage 0 f₀).fields)),
            (∀f₀,Source (O.original f₀) (orig f₀) O.beforeLanes
              ((rc).preparedImage (u).book (u).bookFits measured)) ∧
            (∀r j,(orig false r j).val=(DescentPaidResidentCount.Reset.savedInput B input.valid.host
              (DescentPaidResidentCount.Reset.root_snapshot B input.valid.host (imageOf degreeAt capAt).receiver
                (imageOf degreeAt capAt).book (imageOf degreeAt capAt).prepared measured hdr xs) r (j.cast groupAt)).val) ∧
            (∀r j,(orig true r j).val=(DescentSIMDLookup.encode (u).roots.field
                (DescentRotorWindowArchive.count input.placement.degree (2^((Z).k-(T).commonDepth)) input.placement.cap)
                (ClosedReset.Window.calendar_sender_matrix B (2^e) (u).roots.field (imageOf degreeAt capAt).receiver
                  (imageOf degreeAt capAt).book (imageOf degreeAt capAt).prepared measured hdr xs r (j.cast groupAt))).val) ∧
            ∀f₀ j z₀ h₀ g₀,(packets f₀ j z₀ h₀ g₀).val=
              ((DescentSIMDLookup.encode O.oldBits (O.stage 0 f₀).fields).symm
                (orig f₀ ((Z).packetOwner T rank positive h₀) (finProdFinEquiv (g₀,z₀))) j).val :=by
  obtain ⟨μ,measured,dst,won,scan,posted,root,R,seen,self,hRaw,sRaw,xCount,stored⟩:=
    DateInputs.fromNamed_public_origins_at accepted drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
      sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth entryFits low
      score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom capacity pitchOld chosen pitch
      small word ceiling blocksAt hostsAt boardRoom elapsed sorted run positive
  refine ⟨μ,measured,dst,won,scan,posted,root,R,seen,self,hRaw,sRaw,xCount,?_⟩
  intro x
  obtain ⟨menu,digits,read,act₀,reg₀,packets,source,packet_,loads,hdr,xs,root_,groups,orig,
    original,saved,matrix,values⟩:=stored x
  exact ⟨menu,digits,read,act₀,reg₀,packets,source,packet_,loads,hdr,xs,root_,groups,orig,
    original,saved,matrix,values positive⟩

theorem DateInputs.fromNamed_public_values (run : (u).FinalInputs) (positive : 0<HH) :
    ∃(μ : DescentGL.Layout (E).dim) (measured dst : Memory w),HEq μ B.frame.basis ∧
      ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
        (S.groupCount age) venue.degree w).Exec ((entry₀).image mem) measured
        ((a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      (pub).Exec measured dst ticks ∧ heldRoot degreeAt capAt measured ∧
      ∃R : (u).MeasuredChannels (Fintype.card B.next.V),DateInputs.CaptureRoom R dst ∧
      ClosedReset.Window.CapturedSelf B (u) R ∧
      ∃(hRaw : HH=(C₀).placement.oldHosts) (sRaw : rows=(C₀).placement.shapes)
       (xCount : 2^k=(C₀).placement.blocks),∀x : DescentColonies.Block k,
      ∃(menu : (deck_ x).Values head_ gang_) (digits : (deck_ x).casts.bits=(C₀).fallbackBits),
        (u).PublicValuesRead ready dst (x.cast xCount) digits
          (fun j=>((Z).rawAtIndex T rank j).cast (congrArg₂ Nat.mul hRaw sRaw)) menu ∧
        (∀h₀ g₀,(menu.active h₀ g₀).val=((scaled).enabled (occ x) (fun _=>1) h₀ g₀).val) ∧
        (∀j h₀ g₀,(menu.register j h₀ g₀).val=((scaled).enabled (occ x)
          (controlScalar B input.valid.host B.next.valid.host j) h₀ g₀).val) ∧
        ∃packets : rows_ x,menu=(u).issuedPublicValues (x.cast xCount) R B.frame.basis rfl rfl rfl rfl rfl rfl
          menu.active menu.register packets ∧
        (∀f₀ j z₀,menu.packet f₀ j z₀=packets f₀ j z₀) ∧
        (∀f₀ j z₀,let ptr:=(deck_ x).packets.src (deck_ x).packetBase f₀ j z₀
          ptr.Fits w (deck_ x).castBase ∧ Source ptr (packets f₀ j z₀) (deck_ x).casts.lanes
            ((deck_ x).packets.image (deck_ x).packetBase ((u).beforePacketImage ready dst))) :=by
  obtain ⟨μ,measured,dst,won,scan,posted,root_,R,captured,selfWord,hRaw,sRaw,xCount,pages⟩:=
    DateInputs.fromNamed_public_operand_origins accepted drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
      sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth entryFits low
      score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom oldHubRoom capacity pitchOld chosen pitch
      small word ceiling blocksAt hostsAt boardRoom elapsed sorted run positive
  refine ⟨μ,measured,dst,won,scan,posted,root_,R,captured,selfWord,hRaw,sRaw,xCount,?_⟩
  intro x
  obtain ⟨menu,digits,read,enabled₀,regs₀,packets,exactMenu,stored_,reads,_⟩:=pages x
  exact ⟨menu,digits,read,enabled₀,regs₀,packets,exactMenu,stored_,reads⟩

end NativeReceipt
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
