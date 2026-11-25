import OAI.Hierarchy.DescentDatedSortedOperandProgram
import OAI.Hierarchy.DescentDatedOperandHeadTransfer
import OAI.Hierarchy.DescentDatedOperandSignedHeads
import OAI.Hierarchy.DescentDatedOperandCasts
import OAI.Hierarchy.DescentOperandSelectorWidth
import OAI.Hierarchy.DescentDatedMouthPersistence
import OAI.Hierarchy.DescentDatedSignedInput

namespace OAI
/-! # Original native preparation and eight expressions for each dated operand -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentRawCablePanel DescentHaloWalkRAM
open DescentSIMDLookup DescentSharedCableNames DescentPackedZip DescentOrdinaryAtomFieldRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "e" => v.material
local notation "s" => v.signed
local notation "fmt" => v.ticket.depotShape v.short
local notation "P" => breadth (fmt).degree
local notation "O" => DepotRAM.Material.roles fmt
local notation "l" => v.resolver
local notation "g" => v.ticketReadGeometry
local notation "d" => v.operandShortBits

def operandRootBase (floor : ℕ) :=DescentDatedOperandCasts.stop d (l).lanes (v.headTransferEnd floor)
def preparedUntil (floor : ℕ) :=SortedInput.stop g (v.operandRootBase floor)

def sourceCast (floor : ℕ) :=DescentDatedOperandCasts.expr v.operandWidth d (l).lanes (v.headTransferEnd floor)
def nativeTicketSources (floor : ℕ) (_c : v.SignedChart) (A : v.ArgumentEntry) (match_ : A.Match v floor)
    (shape : v.VectorShape) (blocks : v.resolver.blocks = v.material.blocks) : Sources g :=
  let block:=fun j=>((l).index.symm j).1.cast blocks
  let up:=v.sourceCast floor
  ⟨v.originAt floor d shape,
   fun j f=>up 1 (v.oldHeaderAt floor j f),
   fun j f=>up 2 (v.mouthAt floor A match_ shape j f),
   fun j f i=>up 0 (v.transferredOld floor (block j) f i),
   fun i=>up 3 (v.transferredPath floor i),
   fun j f i=>up 0 (v.transferredAnchor floor (block j) f i),
   fun j f i=>up 0 (v.transferredRaw floor (block j) f i),
   fun i=>up 3 (v.transferredRank floor i)⟩

variable (floor w : ℕ) (c : v.SignedChart) (A : v.ArgumentEntry) (match_ : A.Match v floor)
    (shape : v.VectorShape) (blocks : v.resolver.blocks = v.material.blocks)
def sortedTicketPhase :=SortedInput.program g (v.nativeTicketSources floor c A match_ shape blocks) (v.operandRootBase floor) (e).oldHosts v.materialPitch
  (v.operandRanks floor).endpoints (A.ports v floor).roster w
def originalSourcePhase :=
  ((((v.operandEarlyPhase floor w A).seq (v.headTransferPhase floor c w)).seq
    (DescentDatedOperandCasts.phase v.operandWidth d (l).lanes (v.headTransferEnd floor) w)).seq
    (v.sortedTicketPhase floor w c A match_ shape blocks))

def nativeTicketPreparation (pg : Fin (7*v.vector.operands)) :=
  (v.originAndMouth floor w A match_ d ((A.directory v floor match_).refs pg)).seq
    (v.originalSourcePhase floor w c A match_ shape blocks)

def nativeTicketExpr (j : Fin (l).jobs) (f : Fin 8) := SortedInput.output g (v.nativeTicketSources floor c A match_ shape blocks) (v.operandRootBase floor) j f

theorem prepared_span : v.preparedUntil floor=v.originMouthEnd floor+v.rootSourceSize :=by
  rw [preparedUntil,SortedInput.stop,DescentDatedOperandReadPipeline.endAddress_eq_pipelineWords,SortedInput.adapter_span]
  unfold operandRootBase DescentDatedOperandCasts.stop
  rw [v.head_transfer_span]
  unfold rootSourceSize operandHeaderEnd operandMouthHeaderStart
    operandOldHeaderStart operandRankStart DescentDatedSourcePathDirectory.Local.stop DescentDatedSourcePathDirectory.stop
    DescentSharedLeafLookup.Public.stop DescentDatedSourcePathDirectory.hostEnd DescentDatedSourcePathDirectory.stride operandPathStart
  rw [DescentDatedOperandPages.affine]
  simp only [Nat.zero_add,Nat.add_assoc]
  rfl

theorem grain_after_sources
    (purchased : v.origin.preparationWords=v.originControlWords+v.originMouthWords+v.rootSourceSize) :
    v.origin.grainBase (v.routedStart floor)=v.preparedUntil floor :=by
  rw [v.prepared_span,originMouthEnd,v.originPort_span]
  simp only [DescentDatedPriorOperand.OriginPlan.grainBase,purchased,Nat.add_assoc]

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
