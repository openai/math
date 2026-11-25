import OAI.Hierarchy.DescentFullPriorPad
import OAI.Hierarchy.DescentScheduledResetAtPorts
import OAI.Hierarchy.DescentScheduledEnteredProgram
import OAI.Hierarchy.DescentResetHostPadRegisters
import OAI.Hierarchy.DescentPriorArchiveDate

namespace OAI
/-! The complete physical date pays for reindexing every preceding register page. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSixParty.Chronology DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ)
    (ports : Chronology.DatePorts)
local notation "a" => scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z ports
variable (floor w : ℕ)
local notation "ap" => (a) floor
local notation "L" => (ap).inner.successor.setup.retained
/-- All source widths and row strides belong to the actual preceding archive.
Only the fields used by the metadata and seven-operand reader are replaced. -/
def previousArchiveLayout : DescentResetRetainedSetup.Layout :=
  { L with
    bits := ports.operandBits
    hosts := ports.operandHosts
    groups := ports.venue.groups
    blocks := 2^k
    previousNodes := ports.nodes
    previousArgs := ports.argumentsPerNode
    previousLanes := ports.operandLanes }

local notation "raw" => previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor

def priorArchivePhase : NativePhase w :=
  ports.fullPad k floor (ports.archive.prior raw) (fun x=>ports.archive.roles.bank x.val) w

local notation "publisher" => priorArchivePhase G S board k tail age p f gain drift degree h ordinary op s Z ports floor w
variable (capacity : ports.venue.cap = ((capCalendar G.b S.rounds gain S.height).take age).prod*256)
    (res : ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
      ports.operandLanes ports.roleLanes ports.venue ports.io (ports.priorStart k floor) w
      (ports.afterPad k floor).archive)
local notation "inside" => scheduledEntered G S board k tail age p f gain drift degree h ordinary op s Z
  ports.operandLanes ports.roleLanes ports.venue ports.io (ports.priorStart k floor) w
  (ports.afterPad k floor).archive capacity res

/-- A single original fixed date from the preceding, possibly shorter archive
through the physically padded archive and the final metadata post. -/
def scheduledPadded : DateCode w := DateCode.withPriorArchive publisher inside

theorem scheduled_padded_price :
    (scheduledPadded G S board k tail age p f gain drift degree h ordinary op s Z ports floor w capacity res).tariff =
    ((publisher).ticks+7*DescentStaticWordColumn.names (publisher).program)*w+(inside).tariff :=
  DateCode.prior_archive_price ..

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
