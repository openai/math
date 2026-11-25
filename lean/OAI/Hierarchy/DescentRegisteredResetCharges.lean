import OAI.Hierarchy.DescentRegisteredResetStep
import OAI.Hierarchy.DescentResetEnteredCharges
import OAI.Hierarchy.DescentNamedResetTailSizes

namespace OAI
/-! The price of the public scheduled opcode uses the predecessor's recorded
history and the same concrete dated inputs that publish the successor ports. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ) (prev : DatePorts) (floor w : ℕ)
local notation "oldExp" => NativePitch.resetCut S k tail p f h age
local notation "nextM" => NativePitch.incoming S k tail p f h ordinary (age+1)
local notation "token" => DescentPrimitivePalette.printedBits G s Z op
local notation "cut" => receiverCut G S board k tail age p f gain drift degree h oldExp nextM op.C op.w
  prev.operandLanes prev.roleLanes token prev.venue
local notation "fits" => scheduled_cut_origin G S board k tail age p f gain drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue
local notation "priorFits" => preceding_cut S k tail p f h age
local notation "a" => DescentDatedAddressBook.PhysicalReset.scheduled G S board k tail age p f gain drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue prev.io.wire prev.io.roster floor
variable (capacity : prev.venue.cap=((capCalendar G.b S.rounds gain S.height).take age).prod*256)
    (space : ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
      prev.operandLanes prev.roleLanes prev.venue prev.io floor w prev.archive)
abbrev innerResetDate : DateCode w :=
  scheduledEntered G S board k tail age p f gain drift degree h ordinary op s Z prev.operandLanes prev.roleLanes
    prev.venue prev.io floor w prev.archive capacity space

def innerResetInputs : (a).DateInputs ((a).stageStart floor) w :=
  DateInputs.fromNamed G S board k tail age p f gain drift degree h cut oldExp (2^cut) nextM op.C op.w
    prev.operandLanes prev.roleLanes token prev.venue prev.io floor w fits fits priorFits prev.archive.count
    prev.archive.nodeBase prev.archive.arguments prev.archive.seed space.prepared space.scene

local notation "u" => innerResetInputs G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space
local notation "z" => FinalInputs.fromArchive G S board k tail age p f gain drift degree h cut oldExp (2^cut)
  nextM op.C op.w prev.operandLanes prev.roleLanes token prev.venue prev.io floor w fits fits priorFits
  prev.archive.count space.prepared space.scene prev.archive s Z op capacity

def resetCharges : EnteredCharges :=enteredCharges (a).ingress floor u prev.io

theorem reset_charge_bound (sizes : FinalInputs.TailSizes (a).successor)
    (roof : (a).successor.primitive.endAddress ((a).successor.birthEnd ((a).rebased ((a).stageStart floor))) < 2^w) :
    (innerResetDate G S board k tail age p f gain drift degree h ordinary op s Z prev floor w capacity space).tariff ≤
      (resetCharges G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space).total :=
  entered_charge_bound (a).ingress floor u z prev.io (Nat.two_pow_pos _) (Nat.two_pow_pos _) (Nat.two_pow_pos _) sizes roof

theorem reset_charge_at (oldLanes : 0 < prev.venue.lanes) (roleLanes : 0 < prev.roleLanes)
    (nextLanes : 0 < nextM) (roof : (a).fullEnd floor < 2^w) :
    (innerResetDate G S board k tail age p f gain drift degree h ordinary op s Z prev floor w capacity space).tariff ≤
      (resetCharges G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space).total := by
  let v:=(a).successor
  let b:=(a).rebased ((a).stageStart floor)
  let prior:=ResetOutput.Prior.atDate G S age p drift prev.operandLanes prev.roleLanes token prev.venue
  have eq : v=ResetOutput.fromBoard G S board k tail age p f gain drift degree h cut oldExp
      (2^cut) nextM op.C op.w prior b :=
    PhysicalReset.named_successor G S board k tail age p f gain drift degree h cut oldExp
      (2^cut) nextM op.C op.w prev.operandLanes prev.roleLanes token prev.venue prev.io.wire prev.io.roster floor
  have sizes : FinalInputs.TailSizes v := by
    rw [eq]
    exact ResetOutput.tail_sizes G S board k tail age p f gain drift degree h cut oldExp
      (2^cut) nextM op.C op.w prior b oldLanes roleLanes (Nat.two_pow_pos _) nextLanes
  have last:v.primitiveEnd b ≤ v.metadataEnd b:=by
    rw [ResetOutput.metadataEnd,v.metadata.translate]
    exact Nat.le_add_right ..
  exact reset_charge_bound G S board k tail age p f gain drift degree h ordinary op s Z prev floor w capacity space
    sizes (last.trans_lt roof)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
