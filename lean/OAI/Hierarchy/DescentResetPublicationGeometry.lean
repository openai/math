import OAI.Hierarchy.DescentRegisteredResetStep
import OAI.Hierarchy.DescentTerminalRegisteredRange
import OAI.Hierarchy.DescentArchiveCellRead
import OAI.Hierarchy.DescentNamedOperandWordRoom

namespace OAI
/-! # Physical dimensions of the archive published by a scheduled reset -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false

section
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (age drift : ℕ)
    (prev out : DatePorts) {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor

/-- The operand, metadata and primitive registers returned by the same physical reset. -/
structure ResetPublicationGeometry : Prop where
  axes : out.rangeLayout=(v).rangeLayout
  chart : out.metadataChart=(v).metadata.chart
  coeff : u.operand.coeff=(v).nodeBits
  small : 2*(v).receiver.candidates<2^(v).receiver.queryBits
  slots : (v).argumentSlots=S.retainedArgumentsAt G drift
  hosts : out.operandHosts=S.hostSize (age+1)
  groups : out.venue.groups=S.groupCount (age+1)
  paidBits : (v).metadata.paidBits=prev.venue.paidBits
  blocks : (v).metadata.chart.blocks≤2^(v).venue.next.k
  roleLanes : out.roleLanes=(v).primitive.chart.lanes
  roleStride : out.archive.roles.stride=(v).primitive.chart.rows
  roleBank : ∀x : Fin (v).primitive.chart.blocks,
    out.archive.roles.bank x.val=(v).primitive.bank ((v).birthEnd (a.rebased floor)) x
  receiverBlocks : (v).receiver.blocks=(v).metadata.chart.blocks
  receiverHosts : (v).receiver.hosts=(v).metadata.chart.hosts
  receiverGroups : (v).receiver.groups=(v).metadata.chart.groups
  receiverLanes : (v).receiver.lanes=(v).metadata.chart.lanes
  operandNodes : u.operand.nodes=(v).metadata.chart.nodes
  operandSlots : u.operand.slots=(v).argumentSlots
  spanBits : u.operand.coeff=(v).metadata.spanBits
  nodeCount : out.nodes=S.retainedNodes
  positiveLanes : 0<out.operandLanes
  radix : out.venue.k=prev.venue.k
end

variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ) (prev : DatePorts) (floor w : ℕ)
local notation "outer" => scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z prev floor
local notation "v" => (outer).inner.successor
local notation "innerFloor" => prev.priorStart k floor
local notation "previous" => (prev.afterPad k floor).archive
variable (space : ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue prev.io (prev.priorStart k floor) w (prev.afterPad k floor).archive)
local notation "inputs" => resetInputs G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space
local notation "ports" => resetPorts G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space

set_option maxHeartbeats 800000 in
theorem reset_publication_geometry (oldK : prev.venue.k=k) :
    ResetPublicationGeometry G S age drift prev ports inputs where
  axes := PhysicalReset.scheduled_range_layout G S board k tail age p f gain drift degree h ordinary op s Z
    prev.operandLanes prev.roleLanes prev.venue prev.io.wire prev.io.roster innerFloor
    ((outer).inner.stageStart innerFloor) inputs oldK
  chart := congrArg (fun blocks => (⟨blocks,(v).nodes,(v).sheets.hosts,(v).sheets.groups,
      (v).nodeBits,(v).receiver.lanes⟩ : DescentDatedNodeMetadata.Chart)) (congrArg (2^·) oldK)
  coeff := rfl
  small := (Nat.lt_succ_self (2*(v).receiver.candidates)).trans_le (Nat.le_pow_clog (by decide : 1<2) _)
  slots := rfl
  hosts := rfl
  groups := rfl
  paidBits := rfl
  blocks := by
    change 2^k≤2^prev.venue.k
    rw [oldK]
  roleLanes := rfl
  roleStride := rfl
  roleBank _ := rfl
  receiverBlocks := rfl
  receiverHosts := rfl
  receiverGroups := rfl
  receiverLanes := rfl
  operandNodes := rfl
  operandSlots := rfl
  spanBits := rfl
  nodeCount := rfl
  positiveLanes := Nat.two_pow_pos _
  radix := rfl

local notation "oldExp" => NativePitch.resetCut S k tail p f h age
local notation "nextM" => NativePitch.incoming S k tail p f h ordinary (age+1)
local notation "tokenBits₀" => DescentPrimitivePalette.printedBits G s Z op
local notation "cut" => receiverCut G S board k tail age p f gain drift degree h oldExp nextM op.C op.w
  prev.operandLanes prev.roleLanes tokenBits₀ prev.venue
local notation "fits" => scheduled_cut_origin G S board k tail age p f gain drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue

/-- The issued query, operand and signed-candidate words all fit at the receiver's actual pitch. -/
theorem reset_operand_word_room (ready : (inputs).Ready) :
    (v).receiver.queryBits*(v).receiver.lanes≤w ∧
    (inputs).operand.coeff*(v).receiver.lanes≤w ∧
    (v).receiver.signedBits*(v).receiver.lanes≤w :=
  DateInputs.named_amount_rooms G S board k tail age p f gain drift degree h cut oldExp (2^cut) nextM op.C op.w
    prev.operandLanes prev.roleLanes tokenBits₀ prev.venue prev.io innerFloor w fits fits
    (preceding_cut S k tail p f h age) (previous).count (previous).nodeBase (previous).arguments (previous).seed
    space.prepared space.scene ready

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
