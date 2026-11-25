import OAI.Hierarchy.DescentNamedEnteredProgram
import OAI.Hierarchy.DescentScheduledResetChart
import OAI.Hierarchy.DescentPriorResetArchive

namespace OAI
/-! # The scheduled reset instruction, clock and scratch intervals are fixed before the tape is read -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
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

theorem scheduled_cut_origin : cut≤oldExp :=by
  change min (min oldExp (min _ _)) _≤oldExp
  exact (min_le_left ..).trans (min_le_left ..)

theorem preceding_cut (age : ℕ) : NativePitch.resetCut S k tail p f h age≤S.groupWidth k tail age :=by
  have dim : laneBits (S.groupWidth k tail age+k) h
    (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))≤S.groupWidth k tail age+k:=min_le_left ..
  unfold NativePitch.resetCut
  dsimp only
  omega

local notation "fits" => scheduled_cut_origin G S board k tail age p f gain drift degree h ordinary op s Z
  operandLanes primitiveLanes old
local notation "priorFits" => preceding_cut S k tail p f h age
variable (floor w : ℕ) (history : PriorResetArchive)
local notation "count₀" => history.count
local notation "support" => NamedCodeRoom G S board k tail age p f gain drift degree h cut oldExp (2^cut)
  nextM op.C op.w operandLanes primitiveLanes token old io floor w fits fits priorFits count₀
variable (capacity : old.cap=((capCalendar G.b S.rounds gain S.height).take age).prod*256)

abbrev ScheduledCodeRoom := support

/-- The three concrete constructors of the earlier archive are the seed, ordinary date and reset date.
Both lanes of a branch decision enter this identical instruction. -/
def scheduledEntered (space : support) : DateCode w :=
  namedEntered G S board k tail age p f gain drift degree h cut oldExp (2^cut) nextM op.C op.w
    operandLanes primitiveLanes token old io floor w fits fits priorFits count₀ history.nodeBase history.arguments
    history.seed history.roles s Z op capacity space

local notation "code" => scheduledEntered G S board k tail age p f gain drift degree h ordinary op s Z
  operandLanes primitiveLanes old io floor w history capacity

/-- Two histories of the same age that share the earlier public address register issue the same code. -/
theorem scheduled_entered_same (space₁ space₂ : support) : code space₁=code space₂ :=rfl

theorem scheduled_entered_original (space : support) :
    let a:=plan floor
    ∃ (u : (atIngress a.ingress floor a rfl rfl).DateInputs (a.stageStart floor) w) (z : u.FinalInputs),
      code space=entered a.ingress floor rfl rfl u z io.hubs
        (fun x=>io.atoms x.val) (fun j=>io.wire j.1.val j.2.val) :=by
  obtain ⟨u,z,_,_,physical⟩:=namedEntered_issued G S board k tail age p f gain drift degree h cut oldExp (2^cut)
    nextM op.C op.w operandLanes primitiveLanes token old io floor w fits fits priorFits count₀
    history.nodeBase history.arguments history.seed history.roles s Z op capacity space
  exact ⟨u,z,physical⟩

local notation "u₀" sp => DateInputs.fromNamed G S board k tail age p f gain drift degree h cut oldExp (2^cut)
  nextM op.C op.w operandLanes primitiveLanes token old io floor w fits fits priorFits count₀
  history.nodeBase history.arguments history.seed (NamedCodeRoom.prepared sp) (NamedCodeRoom.scene sp)
local notation "z₀" sp => FinalInputs.fromArchive G S board k tail age p f gain drift degree h cut oldExp (2^cut)
  nextM op.C op.w operandLanes primitiveLanes token old io floor w fits fits priorFits count₀
  (NamedCodeRoom.prepared sp) (NamedCodeRoom.scene sp) history s Z op capacity

/-- Every original lower workspace address is retained even on an arbitrary malformed input tape. -/
theorem scheduled_entered_any (space : support) (ready : (u₀ space).Ready) (last : (z₀ space).Room)
    (safeHub : io.hubs.Fits w floor)
    (safeAtoms : ∀x : Fin (2^(plan floor).ingress.k),(io.atoms x.val).Fits w floor)
    (safeWires : ∀j : (plan floor).ingress.signed.Slot,(io.wire j.1.val j.2.val).Fits w floor)
    (address : (plan floor).stageStart floor<2^w) (m : Memory w) :
    ∃out : Memory w,(code space).Runs m out ∧ (code space).cheap ∧
      ∀j,j<floor ∨ (plan floor).fullEnd floor≤j→ out j=m j :=
  enterCode_any (plan floor).ingress floor (u₀ space) (z₀ space) io safeHub safeAtoms safeWires address ready last m

theorem scheduled_entered_fee (space : support) :
    let initial:=(plan floor).ingress.phase floor w io.hubs (fun x=>io.atoms x.val)
      (fun j=>io.wire j.1.val j.2.val)
    (code space).tariff=(initial.ticks+7*DescentStaticWordColumn.names initial.program)*w+
      (date (z₀ space)).tariff :=
  enterCode_price (plan floor).ingress floor (u₀ space) (z₀ space) io

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
