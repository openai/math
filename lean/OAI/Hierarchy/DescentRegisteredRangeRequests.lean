import OAI.Hierarchy.DescentOriginalFreshInputs
import OAI.Hierarchy.DescentIssuedRangeRequests

namespace OAI
/-! # The range table read on the actual posted reset actor state -/
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
local notation "C₀" => (v).setup
local notation "range_" => DateInputs.RangeRequestsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
local notation "panels_" => DateInputs.OperandPanelsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom

set_option hygiene true
set_option maxHeartbeats 1200000
set_option maxRecDepth 6144
theorem DateInputs.range_requests_at_actors
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
    (ready : (u).Ready) (m actors : Memory w) (archived : (C₀).retained.Values)
    (issued : (u).ThroughActors ((entry₀).image m) actors) (held : panels_ degreeAt capAt ready m archived) :
    ∃(μ : DescentGL.Layout (E).dim) (measured : Memory w),HEq μ B.frame.basis ∧
      measured (P).saved=((DescentExterior.matrixCode μ).val:Word w) ∧
      ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
        count (E).depthRows (rc).stencil book measured ∧
      (pub).Exec measured actors ticks ∧ range_ degreeAt capAt ready archived μ measured actors :=by
  obtain ⟨μ,measured,dst,chosen,savedCode,panel,scan,publish,requests,_⟩:=held
  have reached : (u).ThroughActors ((entry₀).image m) dst:=(DateInputs.classified_prefix («u»:=(u)) ready scan publish).1
  have same : dst=actors:=ProtocolRAM.exec_unique _ _ _ _ reached issued
  subst dst
  exact ⟨μ,measured,chosen,savedCode,panel,publish,
    DateInputs.range_requests_of_issued (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom degreeAt capAt ready archived μ measured actors requests⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
