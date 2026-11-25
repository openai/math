import OAI.Hierarchy.DescentOriginalBoardFields

namespace OAI
/-! # Original public operand rows on the reached actor snapshot -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
set_option maxRecDepth 6144
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
variable (fitsStencil : e ≤ laneBits (S.groupWidth k tail age+k) payload
  (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k)
  (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
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
set_option hygiene false
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
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

local notation "x" => x₀.cast (I).operandBlocks
local notation "ctrl" => (v).controlRegisters
local notation "controls" => (v).controlFloor base₀
local notation "actor" => (v).actor
local notation "origin" => (v).middle.stop base₀
local notation "active" => (ctrl).live controls (x).val
local notation "reg" => (ctrl).ports controls ((a).c/2) (x).val ((actor).directory origin).inverse
    ((actor).depths origin) ((actor).levels origin)
local notation "ports" => OperandMenu.publicPorts («a»:=(a)) (I).shape start (I).count (I).hub (I).g (I).Y active reg

open DescentResetPublicOperandBook
local notation "rows" => (roster (Z).graph ((Z).k-(T).commonDepth) (GroupStage.depthBound D n f g)).card
local notation "K" => publicOperandConfig B (hw).rotorBits (hw).queryBits M (B.reset.unit/p) (B.reset.unit/p)
  S.retainedNodes (S.retainedArgumentsAt G drift) p
local notation "printedRow" menu:arg rh:arg rg:arg => (I).menu.publicData (I).shape start (I).count (I).hub (I).g (I).Y
  active reg menu rfl (x).val rh rg

set_option hygiene true

/-- The actual menu and an observation at one of its native host/group coordinates. -/
def DateInputs.ObservedFreshRow
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (ok : (I).Ready) (actorMem : Memory w) (x₀ : Fin (v).receiver.blocks)
    (size : (S.hostSize age)*rows=(hw).placement.sparse) (shape:(cfg)=K)
    (rh:Fin hh) (rg:Fin gg) (observation:(K).Data (Z).n→Prop) : Prop :=
  ∃ menu:(ports).Values hh gg,
    (I).PublicValuesRead ok actorMem x rfl (fun j:Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast size) menu ∧
    observation (Config.relabel shape B.dimension.symm (printedRow menu rh rg))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
