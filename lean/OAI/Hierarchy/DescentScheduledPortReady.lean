import OAI.Hierarchy.DescentScheduledResetFromPorts
import OAI.Hierarchy.DescentScheduledSelectedReady

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z operandLanes primitiveLanes : ℕ)
    (ports : Chronology.DatePorts)
local notation "old" => ports.venue
local notation "io" => ports.io
local notation "oldExp" => NativePitch.resetCut S k tail p f h age
local notation "nextM" => NativePitch.incoming S k tail p f h ordinary (age+1)
local notation "token" => DescentPrimitivePalette.printedBits G s Z op
local notation "cc" => S.groupWidth k tail age
local notation "cut" => receiverCut G S board k tail age p f gain drift degree h oldExp nextM op.C op.w
  operandLanes primitiveLanes token old
local notation "plan" => scheduled G S board k tail age p f gain drift degree h ordinary op s Z operandLanes
  primitiveLanes old (io).wire (io).roster
local notation "cap" => ((capCalendar G.b S.rounds gain S.height).take age).prod*256

local notation "fits" => scheduled_cut_origin G S board k tail age p f gain drift degree h ordinary op s Z
  operandLanes primitiveLanes old
local notation "priorFits" => preceding_cut S k tail p f h age
variable (floor w : ℕ)
local notation "history" => ports.archive
local notation "count₀" => (history).count
local notation "support" => NamedCodeRoom G S board k tail age p f gain drift degree h cut oldExp (2^cut)
  nextM op.C op.w operandLanes primitiveLanes token old io floor w fits fits priorFits count₀

local notation "expect" => NamedEntrySpace G S board k tail age p f gain drift degree h cut oldExp (2^cut)
  nextM op.C op.w operandLanes primitiveLanes token old io floor w count₀
local notation "v" => ((plan) floor).successor
local notation "Q" => S.endpointBook k tail age p f (old).degree h n
local notation "oldWord" => S.localWalshBits p (cc+k) f (quota S.rounds)


theorem scheduled_port_ready (homes : (old).hosts=S.hostSize age) (blocks : (old).k=k)
    (capacity : (old).cap=cap) (groupsOld : (old).groups=S.groupCount age) (lanesOld : (old).lanes=2^oldExp)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k) (within : age<S.length)
    (header : ports.HeaderRoom w floor) (wires : ports.WireRoom w floor)
    (short : 8*(v).groupWidth≤h) (bus : h≤w) (degreeRoom : (old).degree+1<2^w)
    (top : ((plan) floor).fullEnd floor<2^w)
    (oldExtent : (history).Fits (v).setup.retained floor)
    (paid : ports.PaidRoom w floor)
    (columns : (v).roleTransfer.transfer.blocks≤(history).roles.blocks)
    (archive : (history).roles.endAddress≤floor) (res : support) :
    ScheduledReady G S board k tail age p f gain drift degree h ordinary op s Z operandLanes
      primitiveLanes old io floor w history capacity res :=by
  have entry:=scheduled_port_entry G S board k tail age p f gain drift degree h ordinary op s Z
    operandLanes primitiveLanes ports floor w homes blocks capacity groupsOld lanesOld groups radix header wires
    short bus degreeRoom top
  exact scheduled_ready_fields G S board k tail age p f gain drift degree h ordinary op s Z
    operandLanes primitiveLanes old io floor w history capacity entry res homes blocks within oldExtent
    paid.issued paid.stock columns archive

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
