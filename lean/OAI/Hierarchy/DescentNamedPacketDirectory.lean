import OAI.Hierarchy.DescentNamedPacketRankEntry
import OAI.Hierarchy.DescentNamedOperandActorGeometry

namespace OAI
/-! # Literal actor directory dimensions for a selected reset -/
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

open DescentSortedRoster
local notation "prior_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "rawRows" => (⟨(U).endAddress actorBase,HH,rows,chunks (2^(T).commonDepth) (2^e)⟩ :
  DescentResetNewActorDirectory.Layout)

private theorem actor_end_contains_base (actorSetup : ActorSetup) (base : ℕ) :
    base ≤ actorSetup.endAddress base := by
  simp only [ActorSetup.endAddress,ActorSetup.scene,ActorSetup.gate,ActorSetup.next,ActorSetup.bank,
    ActorSetup.heights,ActorSetup.levels,ActorSetup.starts,ActorSetup.counts,ActorSetup.depths,
    Bank.size,DescentSharedLeafLookup.Public.stop,Nat.add_assoc]
  exact Nat.le_add_right _ _

theorem DateInputs.fromNamed_packet_directory (degreeAt : venue.degree=D) (blocksAt : venue.k=k)
    (hostsAt : venue.hosts=HH) (capAt : input.placement.cap=cap) (nextLanes : 0<M)
    (ready : (dateInput).Ready) :
    dir=rawRows ∧ (scene).Fits w ((U).endAddress actorBase) ∧
    HH*rows*chunks (2^(T).commonDepth) (2^e)≤ (scene).size ∧
    chunks (2^(T).commonDepth) (2^e)≤2^w ∧ (rawRows).endAddress<2^w ∧ actorBase≤(U).endAddress actorBase:=by
  obtain ⟨_,_,_,hosts,shapes,parts,_⟩:=ClosedReset.Window.named_operand_geometry B p drift degree payload e previous
    M nextM packet prior_ base₀ degreeAt blocksAt hostsAt capAt nextLanes
  have eqn : dir=rawRows:=by
    change DescentResetNewActorDirectory.Layout.mk _ (U).hosts (U).shapes (U).chunksPerHost=_
    exact congrArg₂ (fun (hs : ℕ × ℕ) parts => DescentResetNewActorDirectory.Layout.mk
      ((U).endAddress actorBase) hs.1 hs.2 parts) (show ((U).hosts, (U).shapes) = (HH, rows) from Prod.ext hosts shapes) parts
  have high : (U).endAddress actorBase≤(U).directoryEnd actorBase:=Nat.le_add_right ..
  have bound : (U).endAddress actorBase<2^w:=high.trans_lt ready.actor.room
  have size : (scene).Fits w ((U).endAddress actorBase):=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left (scene).size (scene).base).trans_lt bound,le_rfl⟩
  have counts := (congrArg₂ Nat.mul shapes (congrArg₂ Nat.mul hosts parts)).symm.trans_le ((U).extent_scene actorBase)
  have floorBefore := actor_end_contains_base U actorBase
  have sameCount : HH*rows*chunks (2^(T).commonDepth) (2^e) = rows*(HH*chunks (2^(T).commonDepth) (2^e)) := by ring
  exact ⟨eqn,size,sameCount.trans_le counts,
    parts ▸ ready.actor.parts,eqn ▸ ready.actor.room,floorBefore⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
