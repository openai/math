import OAI.Hierarchy.DescentRegisteredResetCharges
import OAI.Hierarchy.DescentNamedOriginalFactor
import OAI.Hierarchy.DescentResetOriginalDatePrice
import OAI.Hierarchy.DescentResetRootPitchRows
import OAI.Hierarchy.DescentNamedResetPreflight

namespace OAI
/-! The original share of the registered reset price, including its actual mounted predecessor. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ) (prev : DatePorts) (floor w : ℕ)
local notation "cap" => ((capCalendar G.b S.rounds gain S.height).take age).prod*256
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
variable (space : ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
    prev.operandLanes prev.roleLanes prev.venue prev.io floor w prev.archive)
local notation "u" => innerResetInputs G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space

local notation "v" => (a).successor
local notation "b₀" => (a).rebased ((a).stageStart floor)
local notation "src" => (v).actorEnd b₀
local notation "c₀" => S.groupWidth k tail age
local notation "bits₀" => S.localWalshBits p (c₀+k) f (quota S.rounds)
local notation "D₀" => prev.venue.degree
local notation "Ht" => GroupStage.depthBound D₀ n f gain
local notation "Y₀" => (2^n : ℕ)
local notation "Z₀" => (2^Ht : ℕ)
local notation "P₀" => DescentResetCableSlots.cableCap board Ht
local notation "A₀" => 2*((Y₀+1)+((2*d+4)*Y₀+(Y₀+1)*2^(Ht+1)))
local notation "growth" => 2^S.hostGain*S.radix
local notation "factor" => OriginalControlPrice.factorBound D₀ Y₀ Z₀ P₀ A₀ (2^k) cap growth
local notation "R" => (v).remap b₀
local notation "Zc" => resetCharges G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space

theorem numbered_volume (live : age<S.length) (groups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (dim : (c₀+k+1)^2≤h/2) (short : 8*(v).groupWidth≤h) (roof : (a).fullEnd floor<2^w)
    :
    (Zc).numbered ≤ (factor*ResetOutput.receiptArea h (S.hostSize age) (chunks (S.groupCount age) (2^cut)))*w :=by
  have inventory := PhysicalReset.selected_inventory G S board k tail age p f gain drift degree h oldExp nextM
    op.C op.w prev.operandLanes prev.roleLanes token prev.venue prev.io.wire prev.io.roster floor
  have inputWidth := short
  unfold ResetOutput.groupWidth at inputWidth
  rw [show (v).rootUnits = _ from inventory.1, show (v).receiverUnits = _ from inventory.2.1] at inputWidth
  have markers:=PhysicalReset.named_marker_end G S board k tail age p f gain drift degree h cut oldExp
    (2^cut) nextM op.C op.w prev.operandLanes prev.roleLanes token prev.venue prev.io floor w
    fits fits priorFits prev.archive.count space.scene
  have fee:=PhysicalReset.original_priced G S board k tail age p f gain drift degree h cut oldExp
    (2^cut) nextM op.C op.w prev.operandLanes prev.roleLanes token prev.venue prev.io floor w
    fits fits priorFits prev.archive.count prev.archive.nodeBase prev.archive.arguments prev.archive.seed
    space.prepared space.scene rfl live groups radix dim roof markers (fun t ht=>
      PhysicalReset.selected_room G S board k tail age p f gain drift degree h oldExp nextM op.C op.w
        prev.operandLanes prev.roleLanes token prev.venue prev.io.wire prev.io.roster floor t inputWidth (Or.inr ht))
  exact Nat.mul_le_mul_right w fee

theorem numbered_charge (localRate receiver lead exponent saving : ℕ)
    (quote : ∀ H G₀ stages X capacity increase b width rows fee : ℕ,
      X≤TerminalScale.scale S.height localRate → capacity≤TerminalScale.scale S.height localRate →
      increase≤TerminalScale.scale S.height localRate → b≤TerminalScale.scale S.height localRate →
      width≤TerminalScale.scale S.height receiver → rows*h≤(2+X)*h+G₀*(32*X*b+16*width) →
      fee≤OriginalControlPrice.factorBound D₀ Y₀ Z₀ P₀ A₀ X capacity increase*ResetOutput.receiptArea h H rows →
      1≤ stages → fee*w≤H*h*(lead*TerminalScale.scale S.height exponent)+
        H*(G₀*stages)*(lead*TerminalScale.scale S.height exponent)+S.initialSites/(2^S.height)^saving)
    (live : age<S.length) (groups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (dim : (c₀+k+1)^2≤h/2) (localRoom : 8*bits₀≤h) (short : 8*(v).groupWidth≤h)
    (roof : (a).fullEnd floor<2^w)
    (window : 2^k≤TerminalScale.scale S.height localRate) (count : cap≤TerminalScale.scale S.height localRate)
    (increase : growth≤TerminalScale.scale S.height localRate) (digits : bits₀≤TerminalScale.scale S.height localRate)
    (width : (v).groupWidth≤TerminalScale.scale S.height receiver) :
    (Zc).numbered≤S.hostSize age*h*(lead*TerminalScale.scale S.height exponent)+
      S.hostSize age*(S.groupCount age*S.radix)*(lead*TerminalScale.scale S.height exponent)+
        S.initialSites/(2^S.height)^saving :=by
  have number:=numbered_volume G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space
    live groups radix dim short roof
  let scans:=chunks (S.groupCount age) (2^cut)
  let total:=factor*ResetOutput.receiptArea h (S.hostSize age) scans
  have next : S.groupWidth k tail (age+1)=c₀-k:=by
    have step:=ResetOutput.next_difference S k tail age live
    omega
  have pos : 0<bits₀:=by unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
  have rows : scans*h≤(2+2^k)*h+S.groupCount age*(32*2^k*bits₀+16*(v).groupWidth):=by
    dsimp only [scans]
    rw [←S.group_power groups radix age]
    have inventory := PhysicalReset.selected_inventory G S board k tail age p f gain drift degree h oldExp nextM
      op.C op.w prev.operandLanes prev.roleLanes token prev.venue prev.io.wire prev.io.roster floor
    have paidCut : cut = (v).exponent oldExp oldExp (S.groupWidth k tail (age+1)) h := by
      unfold PhysicalReset.receiverCut ResetOutput.exponent ResetOutput.groupWidth
      rw [show (v).rootUnits = _ from inventory.1, show (v).receiverUnits = _ from inventory.2.1]
      rfl
    rw [paidCut,next]
    exact (v).boundary_rows c₀ k h bits₀ pos localRoom short
  exact number.trans (quote _ _ S.radix (2^k) cap growth bits₀ (v).groupWidth scans total
    window count increase digits width rows le_rfl (by rw [radix];exact Nat.two_pow_pos _))

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
