import OAI.Hierarchy.DescentRegisteredResetHeaders
import OAI.Hierarchy.DescentOriginalFreshHeader
import OAI.Hierarchy.DescentOriginalFreshHost
import OAI.Hierarchy.DescentNamedFreshMenus
import OAI.Hierarchy.DescentOriginalFreshInputs

namespace OAI
/-! # The four registered header words of every live fresh reset argument -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F Pin : Type} [Field F] {d : ℕ} {abits : Pin→ℕ} {W : MarkedWorld F d Pin abits}
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
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "datedInput" pr:arg sc:arg => I₀ previousMeta previousArguments initial pr sc
set_option hygiene false
local notation "u" => datedInput prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

open DescentSortedRoster

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open DescentSharedCableNames
open DescentResetTrunks

local notation "I" => u
open DescentPackedZip DescentResetOperandSetup

local notation "hw" => (v).setup
local notation "r₀" => (hw).retained
local notation "hh" => (hw).placement.newHosts
local notation "gg" => (hw).placement.groups
local notation "cfg" => publicOperands (I).atlas (I).roots (I).menu.payload


open DescentResetPublicOperandBook
local notation "rows" => (roster (Z).graph ((Z).k-(T).commonDepth) (GroupStage.depthBound D n f g)).card
local notation "K" => publicOperandConfig B (hw).rotorBits (hw).queryBits M (B.reset.unit/p) (B.reset.unit/p)
  S.retainedNodes (S.retainedArgumentsAt G drift) p

open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler
open DescentResetTrunks DescentRotor DescentChosenRouter DescentRouterBank DescentResetAttachments
open DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
local notation "split_" => geoShape.granular B.count (z*G.b) B.fit hp (B.unit ▸ pos) (B.unit ▸ whole)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "installed" => reentryWorldShape split_ B.reset B.terminals birth _ hp splitEq (resetMenu B) one hwWide
local notation "after_" => WorldShape.follow hp pos whole B.reblock B.cuts installed
local notation "next_" => (resetArchive B p hp whole priorArchive).bit
local notation "geo" => B.reset.counts_fit B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "tape" => B.reset.nativeResetEdges B.terminals vertexCode birth
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (age+1))) dense) B.valid.coordinates
local notation "sparse" => DescentResetLocalOrder.allCode B.raw ((tape).order.trans Fin.valEmbedding) S B.valid rawSite

open DescentSharedCableNames DescentParallelBase DescentNextSignedWindow DescentOperandStateBanks

open ClosedReset.Window Chronology.DatePorts DescentRetainedRangeDigits
open DescentDatedPriorOperand DescentResetPublicOperandBook
local notation "realRank" => DescentLocalArchiveOrder.reset B p hp whole priorArchive
local notation "datePorts" => Chronology.DatePorts.reset (a) start (I)
local notation "L₀" => (datePorts).rangeLayout
local notation "L₁" => (v).rangeLayout
local notation "capacity₀" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "oldW" => W.granular B.count (z*G.b) B.fit
local notation "key_" => (oldW).graph.Edge ⊕ (Z).bank.Site
local notation "obsAt" row:arg key:arg => FreshObservation (p:=p) (field:=(hw).rotorBits) (query:=(hw).queryBits)
  (lanes:=M) (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) B row key
local notation "issued" => DateInputs.FreshInputsAt (B:=B) drift degree payload e previous M nextM oldLanes
  primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom ok actorMem
local notation "menuAt" block:arg size:arg shape:arg rh:arg rg:arg key:arg => DateInputs.ObservedFreshRow (B:=B) drift degree payload e
  previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
  previousArguments initial prepared sceneRoom ok actorMem block size shape rh rg (fun row=>obsAt row key)

set_option hygiene true
set_option maxHeartbeats 1200000

/-- Acquisition of each earlier register at the occupied original site of its edge or bank. -/
def DateInputs.FreshRowsAt
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (ok : (I).Ready) (actorMem : Memory w) : Prop :=
  ∀(size:(S.hostSize age)*rows=(hw).placement.sparse) (shape:(cfg)=K)
    (hx:(v).receiver.blocks=2^k) (aligned:(v).receiver.hosts=(v).sheets.hosts)
    (groupsAt:(v).receiver.groups=S.groupCount (age+1))
    (block:Fin (v).receiver.blocks) (rh:Fin hh) (rg:Fin gg) (key:key_),
    operandLocation B (block.cast hx) (rh.cast aligned) (rg.cast groupsAt)=some (freshHost B key) →
    menuAt block size shape rh rg key

set_option hygiene false
local notation "seenRows" => DateInputs.FreshRowsAt (B:=B) drift degree payload e previous M nextM oldLanes
  primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom ok actorMem

set_option hygiene true

include accepted in
theorem DateInputs.registered_fresh_headers
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (ok : (I).Ready) (actorMem : Memory w)
    {R : ℕ} (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (hwWide : max 1 (max B.reset.width (C*B.reset.width))≤R) (priorArchive : Archive W)
    (geoShape : WorldShape p R priorArchive.bit)
    (degreeAt:venue.degree=D) (capAt:input.placement.cap=capacity₀)
    (calibrated:z=S.grainAt G.b p (age+1)) (heightPos:0<S.height) (growth:G.b≤2^S.capGain)
    (elapsed:0<age) (sorted:SourceSorted W input.order)
    (oldRank:Local priorArchive.bit) (pin:Pin→ℕ)
    (places:RangeRoom datePorts B.next next_)
    (small:2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (axes:L₀=L₁) (choice:∀i,OrdinalRead (I) ok small actorMem i)
    (issuedInputs:issued) (priorRows:seenRows) :
    SevenOriginHeaders (I) B.next next_ (realRank oldRank) places after_ hp pin ok small axes actorMem choice
      (resetOrigin B hp whole priorArchive) Sum.inr :=by
  obtain ⟨hx,hj,groupsAt,aligned,movement,size,X,strip,sig,marks,fees,archive,printed⟩:=issuedInputs
  obtain ⟨_,boardEq⟩:=DateInputs.fromNamed_public_socket_config (B:=B) accepted drift degree payload e
    previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared sceneRoom degreeAt capAt calibrated
  rw [←funded_units B accepted calibrated] at boardEq
  intro block j f4 h₀ g₀ n₀ y stored inRange which originAt
  let block' := block.cast (congrArg DescentDatedPriorOperand.Layout.blocks axes)
  let arg' := (j.cast (congrArg DescentDatedPriorOperand.Layout.operands axes)).cast ok.slots.symm
  let node' := (n₀.cast (congrArg DescentDatedPriorOperand.Layout.nodes axes)).cast ok.nodes.symm
  let rh:=h₀.cast (congrArg DescentDatedPriorOperand.Layout.hosts axes)
  let rg:=g₀.cast (congrArg DescentDatedPriorOperand.Layout.groups axes)
  have ⟨atHome,numberedAt⟩:=location_at_archive B datePorts next_ (realRank oldRank) places block n₀ h₀ g₀ y stored
    (rh.cast aligned) rfl
  have here:operandLocation B (block'.cast hx) (rh.cast aligned) (rg.cast groupsAt)=
      some (DescentSharedCableNames.Stage.home B.next.placement y.1):=atHome
  have own:=fresh_host_of_slot B hp whole priorArchive y which originAt
  obtain ⟨values,publicRead,observed⟩:=priorRows size boardEq hx aligned groupsAt block' rh rg
    (Sum.map id Sigma.fst which) (here.trans (congrArg some own.symm))
  have inputs:=printed block' arg' node' values publicRead
  let lookup:=(fun f':Fin 7=>choice ((v).operandOrdinal (I).operand f' arg' block' node'))
  obtain ⟨config,semantics⟩:=DateInputs.original_fresh_header (B:=B) accepted drift degree payload e previous M
    nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom ok actorMem block' arg' node' values
    (fun j:Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast size)
    movement.host movement.groups X strip sig marks (fees (block'.cast (I).operandBlocks)) small lookup inputs publicRead
    hx hj groupsAt aligned archive hp one pos whole hwWide priorArchive geoShape degreeAt capAt calibrated heightPos growth
    rh rg oldRank pin (datePorts).argumentsPerNode
  exact semantics y which originAt inRange numberedAt here elapsed sorted observed f4

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
