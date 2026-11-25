import OAI.Hierarchy.DescentScheduledReadyAny
import OAI.Hierarchy.DescentDatePortWireRoom
import OAI.Hierarchy.DescentDatePortHeaderRoom
import OAI.Hierarchy.DescentDatePortPaidRoom

namespace OAI
/-! The preceding numerical chronology supplies the finite input bank bounds for any reset. -/
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


/-- Replace the predecessor branch by its literal date ports. The two native
port bounds are available on initial, ordinary and reset predecessors alike. -/
theorem scheduled_port_entry (homes : (old).hosts=S.hostSize age) (blocks : (old).k=k)
    (capacity : (old).cap=cap) (groupsOld : (old).groups=S.groupCount age) (lanesOld : (old).lanes=2^oldExp)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (header : ports.HeaderRoom w floor) (wires : ports.WireRoom w floor)
    (short : 8*(v).groupWidth≤h) (bus : h≤w) (degreeRoom : (old).degree+1<2^w)
    (top : ((plan) floor).fullEnd floor<2^w) : expect :=by
  apply scheduled_entry G S board k tail age p f gain drift degree h ordinary op s Z operandLanes primitiveLanes
    old io floor w history groups radix short bus degreeRoom header.count.2.2 header.roster.2.2
    (homes ▸ header.peers) header.hubs (homes ▸ header.hosts) _ top
  intro x j
  let y : DescentColonies.Block (old).k:=⟨x.val,by simpa only [blocks] using x.isLt⟩
  let l : Fin (2*(old).cap):=⟨j.val,by simpa only [capacity] using j.isLt⟩
  obtain ⟨fit,area⟩:=wires y l
  exact ⟨fit,by simpa only [homes,groupsOld,lanesOld] using area⟩

/-- The finite program, its public supports, a native execution on every word
tape, and complete preservation outside the single original reset arena. -/
theorem scheduled_port_code (homes : (old).hosts=S.hostSize age) (blocks : (old).k=k)
    (capacity : (old).cap=cap) (groupsOld : (old).groups=S.groupCount age) (lanesOld : (old).lanes=2^oldExp)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k) (within : age<S.length)
    (header : ports.HeaderRoom w floor) (wires : ports.WireRoom w floor)
    (short : 8*(v).groupWidth≤h) (bus : h≤w) (degreeRoom : (old).degree+1<2^w)
    (top : ((plan) floor).fullEnd floor<2^w)
    (oldExtent : (history).Fits (v).setup.retained floor)
    (paid : ports.PaidRoom w floor)
    (columns : (v).roleTransfer.transfer.blocks≤(history).roles.blocks)
    (archive : (history).roles.endAddress≤floor) :
    ∃res : support, ∀m : Memory w,
      let code:=scheduledEntered G S board k tail age p f gain drift degree h ordinary op s Z
        operandLanes primitiveLanes old io floor w history capacity res
      ∃out,code.Runs m out ∧ code.cheap ∧
        ∀j,j<floor ∨ ((plan) floor).fullEnd floor≤j → out j=m j :=by
  have entry:=scheduled_port_entry G S board k tail age p f gain drift degree h ordinary op s Z
    operandLanes primitiveLanes ports floor w homes blocks capacity groupsOld lanesOld groups radix header wires
    short bus degreeRoom top
  let res:=named_code_room G S board k tail age p f gain drift degree h cut oldExp (2^cut) nextM op.C op.w
    operandLanes primitiveLanes token old io floor w fits fits priorFits count₀ entry
  exact ⟨res,scheduled_ready_any G S board k tail age p f gain drift degree h ordinary op s Z
    operandLanes primitiveLanes old io floor w history capacity entry res homes blocks within oldExtent paid.issued paid.stock columns archive⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
