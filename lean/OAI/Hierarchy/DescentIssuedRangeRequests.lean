import OAI.Hierarchy.DescentNamedOperandRequests
import OAI.Hierarchy.DescentNamedIssuedRangeAmount

namespace OAI
/-! # Three range digits from a single measured reset and its original packet -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
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
variable (previousMeta previousArguments : ℕ) (initial : Bool)
set_option hygiene false

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

open DescentSortedRoster
local notation "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "heldRoot" degreeAt:arg capAt:arg measured:arg =>
  (∃hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
        (imageOf degreeAt capAt).book measured,
    ∃x : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host (v).middle.rootField,
      ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
        (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources x nBits tBits)
open DescentSixParty.ClosedReset.Window DescentOperandRootPull DescentSixParty.PackedFlow.Channels
local notation "setup" => (v).setup
local notation "r" => (setup).retained
local notation "at_" => (v).operandFloor base₀
local notation "M₁" => 2^e
local notation "coarse" => (T).commonDepth
local notation "span" => (Z).k-coarse
local notation "field" => (v).middle.rootField
local notation "A₁" => input.placement
local notation "rn₁" => (calendar_residual B).symm
local notation "half₁" => (show (a).c/2=cap by change (2*cap)/2=cap;omega)
local notation "Ksig" => Fin (setup).strip→Fin (setup).placement.oldHosts→Fin ((setup).placement.groups*(setup).placement.blocks)→Cell (setup).signedBits

local notation "ctrl" => (v).controlRegisters
local notation "controlStart" => (v).controlFloor base₀
local notation "liveAt" x:arg => (ctrl).live controlStart (x:Fin (v).receiver.blocks).val
local notation "regsAt" x:arg => (ctrl).ports controlStart ((a).c/2) (x:Fin (v).receiver.blocks).val
  ((U).directory actorBase).inverse ((U).depths actorBase) ((U).levels actorBase)
local notation "deck" x:arg => OperandMenu.publicPorts («a» := (a)) sh start count io.hubs g (2^n) (liveAt x) (regsAt x)
local notation "primaryWords" => DateInputs.PrimaryWordsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
  venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
local notation "primaryCtl" => DateInputs.PrimaryControlsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
  venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
local notation "movementAt" => DateInputs.MovementAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
  venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
local notation "issuedFields" => DateInputs.IssuedFieldsAt G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom
local notation "issuedRead" => DateInputs.fromNamed_issued_ordinal G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom

open DescentSixParty.Chronology.DatePorts
set_option hygiene true
set_option maxHeartbeats 1500000

def DateInputs.RangeRequestsAt
    (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
    (ready : (u).Ready) (old : (r).Values) (μ : DescentGL.Layout (E).dim) (measured actors : Memory w) : Prop :=
    let im:=imageOf degreeAt capAt
    let donor:=(u).menu.donors.trans (congrArg (2^·) rn₁)
    let bound:=(u).menu.capacity.trans ((half₁).trans capAt.symm)
    let which:=fun j:Fin (setup).strip=>(finProdFinEquiv (m:=(r).donors) (n:=2*(setup).oldCap)).symm j
    ∃(hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host im.receiver im.book measured)
      (x : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host field) (X : (setup).seven.Packets) (sig : Ksig)
      (geo : (setup).MovementShape) (dim : (E).dim=(r).high+(r).low) (size : HH*rows=(setup).placement.sparse)
      (hubWord : Fin ((setup).placement.newHosts)→Fin ((setup).placement.groups)→Cell (setup).fieldBits)
      (tickets : Fin ((setup).placement.blocks)→Fin (setup).strip→Fin ((setup).placement.newHosts)→Fin ((setup).placement.groups)→Cell (setup).fieldBits),
      let name:=fun j : Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast size
      let strips:=fun j=>blockValues geo.cut ((r).before geo.size old j) (cast (congrArg DescentGL.Layout dim) μ)
      let inputMem:=(u).beforeSetupImage ready actors
      RootPacket B im.receiver im.book im.prepared measured hdr im.sources x nBits tBits ∧
      (setup).Moved at_ (u).bank name (((setup).sources at_ w (u).bank).image inputMem)
        ((setup).assignedDigits geo.host geo.groups (u).bank.which X strips) sig ∧
      (∀host hi, (X host hi).val=(encode field (DescentRotorWindowArchive.count (A₁).degree (2^span) (A₁).cap)
        (calendar_sender_matrix B M₁ field im.receiver im.book im.prepared measured hdr x host ⟨hi.val,by rw [B.commonDepth];exact hi.isLt⟩)).val) ∧
      (∀j host hi, (sig j host hi).val =
        (((DescentSignedCableCodec.encode (originalCable B x host
          ⟨hi.val,by rw [B.commonDepth,S.group_cut B.age,pow_add,S.group_power ctl.base ctl.radix];exact hi.isLt⟩
          ((which j).1.cast donor) ((which j).2.cast (congrArg (2*·) bound)))).val:Cell field)).val) ∧
      primaryWords ready actors hubWord tickets ∧
      ∀(block : Fin (v).receiver.blocks) (arg : Fin (r).args) (node : Fin (r).nodes)
        (values : (deck block).Values (setup).placement.newHosts (setup).placement.groups),
        ∀(published : (u).PublicValuesRead ready actors (block.cast (u).operandBlocks) rfl name values)
          (small : 2*(v).receiver.candidates<2^(v).receiver.queryBits)
          (choice : ∀axis:Fin 7,OrdinalRead u ready small actors ((v).operandOrdinal (u).operand axis arg block node)),
           0<(v).receiver.lanes → (u).operand.coeff*(v).receiver.lanes≤w →
           (v).receiver.signedBits*(v).receiver.lanes≤w →
           ∀(axis:Fin 3) h gr,
             let page:=DescentRetainedRangeDigits.page axis
             let Y:=(setup).assignedDigits geo.host geo.groups (u).bank.which X strips
             let data:=(u).menu.publicData sh start count io.hubs g (2^n) (liveAt block) (regsAt block)
               values rfl block.val h gr
             let word:=(u).menu.spanValue name Y ((r).outputID 1 page arg node) (block.cast (u).operandBlocks) h gr
               data (finProdFinEquiv (arg,node)) page (published.2.2.2.2.2.1 h gr) (published.2.2.2.2.2.2 h gr)
             ((choice page).amount h gr).val=(word.val:Cell (v).receiver.valueBits).val

theorem DateInputs.range_requests_of_issued
    (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
    (ready : (u).Ready) (old : (r).Values) (μ : DescentGL.Layout (E).dim) (measured actors : Memory w)
    (requests : DateInputs.OperandRequestsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom degreeAt capAt ready old μ measured actors) :
    DateInputs.RangeRequestsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom degreeAt capAt ready old μ measured actors :=by
  obtain ⟨hdr,x,X,sig,geo,dim,size,hubWord,tickets,root,moved,window,signed,controls,issued⟩:=requests
  refine ⟨hdr,x,X,sig,geo,dim,size,hubWord,tickets,root,moved,window,signed,controls,?_⟩
  intro block arg node values published small choice live bus lane axis h gr
  exact DateInputs.named_issued_range_amount G S board k tail age p f g drift degree payload e previous M nextM C
    packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom ready actors block arg node values _ geo.host geo.groups X _ sig
    hubWord (tickets (block.cast (u).operandBlocks)) small (issued block arg node values published) published choice
    live bus lane axis h gr

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
