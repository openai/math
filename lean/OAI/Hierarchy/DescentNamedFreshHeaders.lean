import OAI.Hierarchy.DescentRegisteredFreshHeaders
import OAI.Hierarchy.DescentNamedRelayObservation
import OAI.Hierarchy.DescentNamedFallbackObservation
import OAI.Hierarchy.DescentNamedGoodObservation

namespace OAI
/-! # Fresh original operand headers on the acquired registered reset date -/
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

open DescentResetPublicOperandBook

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

open DescentSharedCableNames DescentParallelBase DescentNextSignedWindow DescentOperandStateBanks

open ClosedReset.Window Chronology.DatePorts DescentRetainedRangeDigits
open DescentDatedPriorOperand DescentResetPublicOperandBook
local notation "realRank" => DescentLocalArchiveOrder.reset B p hp whole priorArchive
local notation "datePorts" => Chronology.DatePorts.reset (a) start (I)
local notation "L₀" => (datePorts).rangeLayout
local notation "L₁" => (v).rangeLayout
local notation "capacity₀" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "issued" => DateInputs.FreshInputsAt (B:=B) drift degree payload e previous M nextM oldLanes
  primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom ok actorMem

local notation "E" => (a).estimator start
local notation "original" dd:arg cd:arg mem:arg mu:arg measured:arg => DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e
  previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  previousMeta previousArguments initial prepared sceneRoom dd ok mem cd mu measured actorMem

local notation "installedSite" whichSide:arg goodRoot:arg => DescentCommonPalette.rotorSiteEquiv B.reset.graph d
  (DescentChosenRouter.selectedRotorLayers B.reset.placement B.reset.graph B.reset.positive B.reset.pay B.reset.circuit whichSide goodRoot)
  C B.reset.width B.reset.unit
set_option hygiene true
set_option maxHeartbeats 1600000

include accepted in
theorem DateInputs.fromNamed_fresh_headers
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (ok : (I).Ready) (actorMem : Memory w)
    {R : ℕ} (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (hwWide : max 1 (max B.reset.width (C*B.reset.width))≤R) (priorArchive : Archive W)
    (geoShape : WorldShape p R priorArchive.bit)
    (degreeAt:venue.degree=D) (capAt:input.placement.cap=capacity₀)
    (calibrated:z=S.grainAt G.b p (age+1)) (heightPos:0<S.height) (growth:G.b≤2^S.capGain)
    (elapsed:0<age) (sorted:SourceSorted W input.order)
    (oldRank:Local priorArchive.bit) (pin:Pin→ℕ) (places:RangeRoom datePorts B.next next_)
    (small:2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (axes:L₀=L₁) (choice:∀i,OrdinalRead (I) ok small actorMem i)
    (issuedInputs:issued) (mem:Memory w) (μ:DescentGL.Layout (E).dim) (measured:Memory w)
    (stored:original degreeAt capAt mem μ measured) :
    SevenOriginHeaders (I) B.next next_ (realRank oldRank) places after_ hp pin ok small axes actorMem choice
      (resetOrigin B hp whole priorArchive) Sum.inr :=by
  apply DateInputs.registered_fresh_headers (B:=B) accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom ok actorMem hp one pos whole hwWide priorArchive geoShape degreeAt capAt calibrated
    heightPos growth elapsed sorted oldRank pin places small axes choice issuedInputs
  intro size shape hx aligned groupsAt block rh rg key located
  rcases key with edge | ⟨⟨s,which⟩,q₀⟩
  · exact DateInputs.relay_observation_at_slot (B:=B) accepted drift degree payload e previous M nextM oldLanes
      primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
      initial prepared sceneRoom degreeAt ok mem capAt calibrated μ measured actorMem stored block size shape hx
      aligned groupsAt rh rg edge located
  · cases which with
    | inl root =>
      obtain ⟨bareSite,rfl⟩ := (installedSite s root).surjective q₀
      exact DateInputs.good_observation_at_slot (B:=B) accepted drift degree payload e previous M nextM oldLanes
        primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
        initial prepared sceneRoom degreeAt ok mem capAt calibrated μ measured actorMem stored growth elapsed sorted
        block size shape hx aligned groupsAt rh rg s root bareSite located
    | inr t =>
      exact DateInputs.fall_observation_at_slot (B:=B) accepted drift degree payload e previous M nextM oldLanes
        primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
        initial prepared sceneRoom degreeAt ok mem capAt calibrated μ measured actorMem stored elapsed sorted
        block size shape hx aligned groupsAt rh rg s t q₀ located

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
