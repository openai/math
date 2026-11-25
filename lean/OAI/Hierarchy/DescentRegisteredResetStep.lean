import OAI.Hierarchy.DescentScheduledPaddedDate
import OAI.Hierarchy.DescentDatedRegisterState

namespace OAI
/-! # The reset instruction and its successor register from one preceding date -/
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
local notation "outer" => scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z prev floor
local notation "a" => (outer).inner
local notation "innerFloor" => prev.priorStart k floor
local notation "previous" => (prev.afterPad k floor).archive
local notation "room" => ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue prev.io innerFloor w previous
variable (capacity : prev.venue.cap = ((capCalendar G.b S.rounds gain S.height).take age).prod*256)
    (space : ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
      prev.operandLanes prev.roleLanes prev.venue prev.io (prev.priorStart k floor) w
      (prev.afterPad k floor).archive)

abbrev resetDate : DateCode w :=
  scheduledPadded G S board k tail age p f gain drift degree h ordinary op s Z prev floor w capacity space

def resetInputs : (a).DateInputs ((a).stageStart innerFloor) w :=
  DateInputs.fromNamed G S board k tail age p f gain drift degree h cut oldExp (2^cut) nextM op.C op.w
    prev.operandLanes prev.roleLanes token prev.venue prev.io innerFloor w fits fits priorFits (previous).count
    (previous).nodeBase (previous).arguments (previous).seed space.prepared space.scene

local notation "inputs" sp => resetInputs G S board k tail age p f gain drift degree h ordinary op s Z prev floor w sp

def resetPorts : DatePorts :=reset (a) ((a).stageStart innerFloor) (inputs space)

local notation "newPorts" sp => resetPorts G S board k tail age p f gain drift degree h ordinary op s Z prev floor w sp
local notation "date" sp => resetDate G S board k tail age p f gain drift degree h ordinary op s Z prev floor w capacity sp

theorem reset_step_same (other : room) : (date space,newPorts space)=(date other,newPorts other) :=rfl

theorem reset_register_count :
    (newPorts space).archive.count=
      ((a).successor.actor.directory ((a).successor.middle.stop ((a).rebased ((a).stageStart innerFloor)))).count :=rfl

theorem reset_register_pitch :
    (newPorts space).venue.lanes=nextM ∧ (newPorts space).roleLanes=(a).successor.primitive.chart.lanes :=⟨rfl,rfl⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
