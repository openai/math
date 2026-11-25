import OAI.Hierarchy.DescentScheduledPaddedReceipt
import OAI.Hierarchy.DescentDatedArchiveWidths

namespace OAI
/-! # The retained-operand reader uses the normalized physical register schema -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSixParty.Chronology DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ)
    (ports : Chronology.DatePorts)
local notation "old" => ports.venue
local notation "io" => ports.io

local notation "a" => scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z ports
variable (floor w : ℕ)
local notation "ap" => (a) floor
local notation "post" => ports.afterPad k floor
local notation "next" => ports.priorStart k floor
local notation "pack" => ports.resetPad k
local notation "L" => (ap).inner.successor.setup.retained
local notation "cap" => ((capCalendar G.b S.rounds gain S.height).take age).prod*256
local notation "support" => ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
  ports.operandLanes ports.roleLanes old io next w (post).archive

local notation "raw" => previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor

local notation "publisher" => priorArchivePhase G S board k tail age p f gain drift degree h ordinary op s Z ports floor w


local notation "loaded" => ({raw with hosts:=(old).hosts} : DescentResetRetainedSetup.Layout)

/-- All fields of the retained reader, including the previous node count,
coincide with the physical padded page layout. -/
theorem scheduled_loaded (width : DatePorts.ArchiveWidths G S op ports k tail p drift degree h age)
    (homes : (old).hosts=S.hostSize age) (groups : (old).groups=S.groupCount age)
    (args : ports.argumentsPerNode=(if age=0 then 3*(S.firstWidth G.b p/p) else S.retainedArgumentsAt G drift)) :
    (loaded)=(L) :=by
  have hn : ports.nodes=(L).previousNodes :=width.nodes
  have ha : ports.argumentsPerNode=(L).previousArgs :=args
  have hb : ports.operandBits=(L).bits :=width.digits
  have hh : (old).hosts=(L).hosts :=homes
  have hg : (old).groups=(L).groups :=groups
  change {(L) with
    bits := ports.operandBits
    hosts := (old).hosts
    groups := (old).groups
    blocks := 2^k
    previousNodes := ports.nodes
    previousArgs := ports.argumentsPerNode
    previousLanes := ports.operandLanes} = (L)
  rw [hn,ha,hb,hh,hg]
  rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
