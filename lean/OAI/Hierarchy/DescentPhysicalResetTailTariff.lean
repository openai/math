import OAI.Hierarchy.DescentPhysicalResetDateTariff
import OAI.Hierarchy.DescentPhysicalFundedCost
import OAI.Hierarchy.DescentFundedSetupInvoice
import OAI.Hierarchy.DescentDatedResetVenuePrice
import OAI.Hierarchy.DescentRetainedHomeMoverTariff
import OAI.Hierarchy.DescentPrimitiveBirthTariff
import OAI.Hierarchy.DescentPrimitiveCheckpointTariff

namespace OAI
/-! Cost of the eight native programs between the rank registers and the published node pages. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSixParty DescentSixParty.Chronology DescentStaticWordColumn DescentSIMDLookup DescentFundedCensus
open DescentGLPacked.BankImage ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
def setupCharge (s : DescentFundedCensus.Setup) (base w : ℕ) :=
  let joins:=s.blocks*(2*2^(SignedFields.joinWidth s.precision s.blocks*s.gatherLanes))
  (109+s.blocks*s.stripCharge)+((4+10*joins)+(8+10*s.printed base w+s.passesTime))+
    7*(15*(joins+1)+(15*(s.printed base w+2)+s.passesNames))+
    ((4+10*2^s.flagWidth)+7*(15*(2^s.flagWidth+1)))

def fundedCharge (s : DescentFundedCensus.Shape) (capacity : ℕ) :=
  let cost:=3*(roleWork capacity+2)+22
  (4+10*(s.pageCount*2^s.width))+(4+s.jobs*(4+s.rows*(2*cost+4)))+
    7*(15*(s.pageCount*2^s.width+1)+(15+s.jobs*(11+4*cost)))

def classCharge (c : DescentResetActorClass.Shape) (base : ℕ) :=
  c.ticks base+7*(15*(c.cells+1)+15*((c.remap base).size+1))

def metadataCharge (c : DescentDatedNodeMetadata.Chart) (a b args : ℕ) :=
  let U:=DescentDatedNodeMetadata.Chart.tallyWork args 7
  4+10*c.setupWords a b+c.bodyClock U+7*(15*(c.setupWords a b+1)+c.bodyNames U)

def originBudget (a : PhysicalReset) :=max 7 (a.successor.birth.argumentBudget 100)

def tailCharge (a : PhysicalReset) (base slots w : ℕ) :=
  let t:=a.successor
  let m:=t.metadata
  setupCharge t.funded (t.finalEnd base) w+fundedCharge t.venue.census t.funded.capacity+
    t.venue.fee+t.roleTransfer.invoice (t.fullEnd base) w+classCharge t.actorClass (t.roleEnd base)+
    t.birth.invoice+(t.primitive.clockBound (originBudget a)+7*t.primitive.nameBound (originBudget a))+
    metadataCharge m.chart m.paidBits m.spanBits slots

structure TailSizes (v : ResetOutput) : Prop where
  oldFunding : 0<v.funded.oldLanes
  gatheredFunding : 0<v.funded.gatherLanes
  oldDense : 0<v.venue.dense.oldLanes
  newDense : 0<v.venue.dense.lanes
  denseBlocks : 0<v.venue.dense.blocks
  oldActors : 0<v.venue.actorLanes
  newActors : 0<v.venue.next.aliveLanes
  newSigned : 0<v.venue.next.signedLanes
  newPaid : 0<v.venue.next.paidLanes
  nextLanes : 0<v.venue.next.lanes
  roleSource : 0<v.roleTransfer.transfer.previousLanes
  roleGather : 0<v.roleTransfer.transfer.gatherLanes
  roleMatrix : 0<v.roleTransfer.transfer.matrixLanes
  roleDecoded : 0<v.roleTransfer.transfer.decodedLanes
  oldPacketLanes : 0<v.roleTransfer.rootLanes
  roleBlocks : 0<v.roleTransfer.blocks
  roleLanes : 0<v.roleTransfer.lanes
  birthSource : 0<v.birth.sourceLanes
  birthBlocks : 0<v.birth.placement.blocks
  birthLanes : 0<v.birth.placement.lanes

variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "F₀" => (v).funded
local notation "V₀" => (v).venue
local notation "Q" => (V₀).census
local notation "M₀" => (v).metadata
local notation "M₁" => (M₀).chart
local notation "stop₀" => (v).finalEnd b
local notation "fund" => (v).fundedEnd b
local notation "roleAt" => (v).fullEnd b
local notation "movedAt" => (v).roleEnd b
local notation "classAt" => (v).classEnd b
local notation "bornAt" => (v).birthEnd b
local notation "move" => (v).roleTransfer
local notation "meta" => (v).primitiveEnd b
local notation "actors" => (v).actor.directory ((v).middle.stop b)
local notation "P" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "key" => (⟨(P).saved,0⟩ : Bank)

theorem origin_operand_work (x j) :
    (z.roles.retained x j).work≤originBudget a ∧ (z.roles.fresh x j).work≤originBudget a ∧
      (z.roles.relay x j).work≤originBudget a :=by
  have vals:=(v).birth.operand_work classAt (j.cast z.birthNodes) (x.cast z.birthBlocks)
    (classWord u) (paid u (x.cast z.censusBlocks))
    (fun i=>z.spans (x.cast z.censusBlocks) (j.cast z.censusNodes) (i.cast z.birthArgs))
    100 (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (fun _=>by exact of_decide_eq_true rfl)
  exact ⟨Nat.le_max_left ..,vals.1.trans (Nat.le_max_right ..),vals.2.trans (Nat.le_max_right ..)⟩

theorem tail_words (sizes : TailSizes v) (space : (v).primitive.endAddress bornAt<2^w) :
    instructionWords z.tailCode z.tailTime≤tailCharge a b u.operand.slots w :=by
  have front:=(F₀).invoice stop₀ w z.earlier key sizes.oldFunding sizes.gatheredFunding
  have counts:=DescentFundedCensus.invoice z.jobs fund w (roleWork (F₀).capacity+2)
    (fun j=>(z.funded_work j).1) (fun j=>(z.funded_work j).2.1) (fun j=>(z.funded_work j).2.2)
  have venue:=(V₀).billed (predecessor u) fund w sizes.oldDense sizes.newDense sizes.denseBlocks sizes.oldActors
    sizes.newActors sizes.newSigned sizes.newPaid sizes.nextLanes
  have prior:=(move).price roleAt w z.previousRoles key (actors).count (actors).inverse z.which (oldMatrix u) (by exact of_decide_eq_true rfl)
    sizes.roleSource sizes.roleGather sizes.roleMatrix sizes.roleDecoded sizes.oldPacketLanes sizes.roleBlocks sizes.roleLanes
  have classNames:=(v).actorClass.priced movedAt z.classKey w
  have born:=(v).birth.price classAt w z.guards (actors).count (actors).inverse
    sizes.birthSource sizes.birthBlocks sizes.birthLanes
  have gate:=(v).primitive.price z.menu.gadget z.menu.stageBits z.menu.grain z.menu.op bornAt z.roles
    (originBudget a) (fun _=>0 : Memory w) z.origin_operand_work space
  have outs:=(M₁).metadataPrice meta (M₀).paidBits (M₀).spanBits w 7 (paid u) z.spans
    (fun _=>by exact of_decide_eq_true rfl) (fun _ _ _=>by exact of_decide_eq_true rfl)
  simp only [instructionWords,tailCode,tailTime,names_seq,classes,DescentResetActorClass.Shape.native,
    tailCharge,setupCharge,fundedCharge,classCharge,metadataCharge] at *
  omega

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
