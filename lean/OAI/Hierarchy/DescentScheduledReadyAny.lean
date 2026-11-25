import OAI.Hierarchy.DescentScheduledEntryReady
import OAI.Hierarchy.DescentNamedFullResetRoom

namespace OAI
/-! The calibrated original reset emits the same code and clock on every raw tape. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z operandLanes primitiveLanes : ℕ)
    (old : StageVenueTail.Date) (io : Dated.Operands)
local notation "oldExp" => NativePitch.resetCut S k tail p f h age
local notation "nextM" => NativePitch.incoming S k tail p f h ordinary (age+1)
local notation "token" => DescentPrimitivePalette.printedBits G s Z op
local notation "cc" => S.groupWidth k tail age
local notation "cut" => receiverCut G S board k tail age p f gain drift degree h oldExp nextM op.C op.w
  operandLanes primitiveLanes token old
local notation "plan" => scheduled G S board k tail age p f gain drift degree h ordinary op s Z operandLanes
  primitiveLanes old io.wire io.roster
local notation "cap" => ((capCalendar G.b S.rounds gain S.height).take age).prod*256

local notation "fits" => scheduled_cut_origin G S board k tail age p f gain drift degree h ordinary op s Z
  operandLanes primitiveLanes old
local notation "priorFits" => preceding_cut S k tail p f h age
variable (floor w : ℕ) (history : PriorResetArchive)
local notation "count₀" => history.count
local notation "support" => NamedCodeRoom G S board k tail age p f gain drift degree h cut oldExp (2^cut)
  nextM op.C op.w operandLanes primitiveLanes token old io floor w fits fits priorFits count₀

local notation "expect" => NamedEntrySpace G S board k tail age p f gain drift degree h cut oldExp (2^cut)
  nextM op.C op.w operandLanes primitiveLanes token old io floor w count₀
local notation "v" => ((plan) floor).successor
local notation "Q" => S.endpointBook k tail age p f old.degree h n
local notation "oldWord" => S.localWalshBits p (cc+k) f (quota S.rounds)


variable (capacity : old.cap=((capCalendar G.b S.rounds gain S.height).take age).prod*256)
local notation "dateInput" sp:arg => DateInputs.fromNamed G S board k tail age p f gain drift degree h cut oldExp (2^cut)
  nextM op.C op.w operandLanes primitiveLanes token old io floor w fits fits priorFits count₀
  history.nodeBase history.arguments history.seed (NamedCodeRoom.prepared sp) (NamedCodeRoom.scene sp)
local notation "finalInput" sp:arg => FinalInputs.fromArchive G S board k tail age p f gain drift degree h cut oldExp (2^cut)
  nextM op.C op.w operandLanes primitiveLanes token old io floor w fits fits priorFits count₀
  (NamedCodeRoom.prepared sp) (NamedCodeRoom.scene sp) history s Z op capacity


/-- With the selected public word budget, the native instruction runs on every
raw tape and preserves exactly the exterior of the whole reset allocation. -/
theorem scheduled_ready_any
    (entry : expect) (res : support) (homes : old.hosts=S.hostSize age) (blocks : old.k=k)
    (within : age<S.length) (oldExtent : history.Fits (v).setup.retained floor)
    (issued : DescentFundedCensus.IssuedBanks io old.hosts old.groups old.lanes)
    (stock : ∀x,(io.atoms x).Fits w floor)
    (columns : (v).roleTransfer.transfer.blocks≤history.roles.blocks)
    (archive : history.roles.endAddress≤floor) (m : Memory w) :
    let code:=scheduledEntered G S board k tail age p f gain drift degree h ordinary op s Z
      operandLanes primitiveLanes old io floor w history capacity res
    ∃out,code.Runs m out ∧ code.cheap ∧
      ∀j,j<floor ∨ ((plan) floor).fullEnd floor≤j → out j=m j :=by
  have all:=DateInputs.named_ready G S board k tail age p f gain drift degree h cut oldExp (2^cut) nextM
    op.C op.w operandLanes primitiveLanes token old io floor w fits fits priorFits count₀ history.nodeBase
    history.arguments history.seed entry res homes within oldExtent.1 oldExtent.2
  have half : ((plan) floor).c/2=cap:=by change (2*cap)/2=cap; omega
  have shape:((plan) floor).RootShape:=by
    refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
    · change 2*cap=2*(((plan) floor).c/2);rw [half]
    · change DescentSignedCableCodec.width old.degree cap=DescentSignedCableCodec.width old.degree (((plan) floor).c/2)
      rw [half]
  have final:=(FinalInputs.fromNamed_original_room G S board k tail age p f gain drift degree h cut oldExp (2^cut)
    nextM op.C op.w operandLanes primitiveLanes token old io floor w fits fits priorFits count₀
    history.nodeBase history.arguments history.seed res.prepared res.scene history.roles s Z op
    capacity shape all homes blocks entry.groups entry.radix within (Nat.two_pow_pos _) issued stock columns
    archive entry.ceiling)
  have early:=((plan) floor).occupied (((plan) floor).stageStart floor)
  have later:=((v).cuts (((plan) floor).rebased (((plan) floor).stageStart floor))).middle
  obtain ⟨_,limit,_⟩:=((plan) floor).entered_bounds floor entry.ceiling
  have stage : ((plan) floor).stageStart floor<2^w:=
    (((early.1.trans early.2.1).trans later).trans (((v).cuts _).actors)).trans_lt limit
  apply scheduled_entered_any G S board k tail age p f gain drift degree h ordinary op s Z
    operandLanes primitiveLanes old io floor w history capacity res all final entry.hubs
    (fun x=>stock x.val) _ stage m
  intro j
  exact (entry.wires j.1 j.2).1

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
