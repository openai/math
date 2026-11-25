import OAI.Hierarchy.DescentNamedResetReady
import OAI.Hierarchy.DescentScheduledEnteredProgram
import OAI.Hierarchy.DescentScheduledEndpointRoom
import OAI.Hierarchy.DescentPriorArchiveLimits

namespace OAI
/-! Select the physical packed and scalar address bounds once for a scheduled reset. -/
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

/-- The degree cap bounds the old numerical smoother even for the empty old graph. -/
private theorem old_smoothing (D : ℕ) : DescentBaseProfile.decayExponent D≤D+1 :=by
  have twice : 2*D≤2^D :=by
    induction D with
    | zero=>decide
    | succ D ih=>
      cases D with
      | zero=>decide
      | succ D=>
        rw [pow_succ]
        omega
  have log:=Nat.log_mono_right (b:=2) twice
  rw [Nat.log_pow (by decide : 1<2)] at log
  exact Nat.add_le_add_right log 1

/-- Select every packed input bound using the actual reset degree and the one
numerical receiver inventory shared by the original grouped calendar. -/
theorem scheduled_entry
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (short : 8*(v).groupWidth≤h) (bus : h≤w) (degreeRoom : old.degree+1<2^w)
    (countBefore : (count₀).base+(count₀).size≤floor) (rosterBefore : io.roster.base+io.roster.size≤floor)
    (rosterRows : S.hostSize age*old.degree≤ io.roster.size) (hubs : io.hubs.Fits w floor)
    (hubRows : S.hostSize age≤ io.hubs.size)
    (wires : ∀(x:DescentColonies.Block k)(j:Fin (2*cap)),(io.wire x.val j.val).Fits w floor ∧
      S.hostSize age*chunks (S.groupCount age) (2^oldExp)≤(io.wire x.val j.val).size)
    (top : ((plan) floor).fullEnd floor<2^w) : expect :=by
  obtain ⟨exponent,width⟩:=scheduled_endpoint G S board k tail age p f gain drift degree h operandLanes
    primitiveLanes old ordinary op s Z io.wire io.roster floor short
  obtain ⟨rootInventory, receiverInventory, _, _⟩ := selected_inventory G S board k tail age p f gain drift degree h
    oldExp nextM op.C op.w operandLanes primitiveLanes token old io.wire io.roster floor
  have inventoryWidth := congrArg₂ (fun x y : List ℕ => 1+(x++y).sum) rootInventory receiverInventory
  change 8*(v).groupWidth≤h at short
  change (v).groupWidth=_ at inventoryWidth
  rw [inventoryWidth] at short
  have room (t : ℕ) (mem : t∈(v).rootUnits) : t*(v).receiver.lanes≤h/2:=
    selected_room G S board k tail age p f gain drift degree h oldExp nextM op.C op.w operandLanes
      primitiveLanes token old io.wire io.roster floor t short (Or.inl mem)
  have bit : 0<(Q).b := by
    change 0<DescentWalshPrecision.bits (cc+k) f (quota S.rounds) (S.censusBits p)
    unfold DescentWalshPrecision.bits;omega
  have coords : (Q).c≤(Q).m:=Nat.le_add_right ..
  have low:=pitch_inside (Q) h bit coords width
  have r : (Q).r=k:=by change cc+k-cc=k;omega
  have digit : 2*(Q).b*2^(Q).r≤ sharedWidth (Q):=Nat.le_max_right ..
  have unit : 2*(Q).b≤2*(Q).b*2^(Q).r:=
    Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have lookup : 8*oldWord≤h:=by
    change 8*(Q).b≤h
    omega
  have marker:=(room ((v).front.contact.fieldBits*8+(v).front.contact.fieldBits)
    (by simp [ResetOutput.rootUnits]))
  have peer:=room (v).front.peer.bits (by simp [ResetOutput.rootUnits])
  have paid : 2^cut*max ((v).front.contact.fieldBits*8) (v).front.peer.bits≤w/2 :=by
    change ((v).front.contact.fieldBits*8+(v).front.contact.fieldBits)*2^cut≤h/2 at marker
    change (v).front.peer.bits*2^cut≤h/2 at peer
    have limit : h/2≤w/2 := Nat.div_le_div_right bus
    rcases le_total ((v).front.contact.fieldBits*8) (v).front.peer.bits with left|right
    · rw [max_eq_right left,mul_comm]
      exact peer.trans limit
    · rw [max_eq_left right,mul_comm]
      exact (Nat.mul_le_mul_right (2^cut) (Nat.le_add_right ..)).trans (marker.trans limit)
  refine ⟨groups,radix,?_,rfl,lookup,bus,degreeRoom,(old_smoothing _).trans_lt degreeRoom,
    countBefore,rosterBefore,rosterRows,hubs,hubRows,wires,exponent,width,room,paid,top⟩
  rw [r] at low
  exact (Nat.le_add_left ..).trans low

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
