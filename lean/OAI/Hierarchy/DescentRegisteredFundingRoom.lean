import OAI.Hierarchy.DescentSelectedFundingInvoice
import OAI.Hierarchy.DescentResetIngressReachedKeys

namespace OAI
/-! Native lookup exponents for the funding phase at the two genuine dated pitches. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentDatedAddressBook DescentCompiler DescentPackedWalsh DescentSIMDLookup ProtocolRAM DescentResetSignedTokens
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
  (board : NonlinearExpanders.Graph n d) (k tb i p f g drift degree h M C packet argLanes roleLanes printed : ℕ)
  (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ)
local notation "cc" => S.groupWidth k tb i
local notation "b" => S.localWalshBits p (cc+k) f (quota S.rounds)
local notation "raw" => resetCut S k tb p f h i
local notation "e" => PhysicalReset.receiverCut G S board k tb i p f g drift degree h raw M C packet argLanes roleLanes printed old
local notation "v" => (PhysicalReset.selected G S board k tb i p f g drift degree h raw M C packet argLanes roleLanes printed old io.wire io.roster floor).successor
local notation "s" => (v).funded

private theorem fundingMembers (out : ResetOutput) :
    out.funded.precision*2^out.middle.rootDepth+out.funded.precision ∈ out.rootUnits ∧
    (out.funded.precision+out.funded.precision)*2^out.middle.rootDepth ∈ out.rootUnits ∧
    out.middle.signedBits*2^out.middle.rootDepth ∈ out.rootUnits ∧
    out.venue.census.broadcast ∈ out.rootUnits := by
  simp [ResetOutput.rootUnits]

private theorem inventoryWidth {out seed : ResetOutput} (roots : out.rootUnits=seed.rootUnits)
    (receivers : out.receiverUnits=seed.receiverUnits) : out.groupWidth=seed.groupWidth := by
  unfold ResetOutput.groupWidth
  rw [roots,receivers]

set_option maxHeartbeats 500000 in
theorem funding_keys_at (live : i < S.length) (blocks : old.k=k)
    (precision : old.paidBits=S.censusBits p) (pitch : old.lanes=2^raw)
    (capacity : old.cap=((capCalendar G.b S.rounds g S.height).take i).prod*256)
    (localRoom : 8*b ≤ h) (rootRoom : 8*(v).groupWidth ≤ h) (dim : (cc+k)*(cc+k) ≤ h/2) :
    (s).oldLanes ≤ h ∧ (s).gatherLanes ≤ h ∧ (s).precision*(s).oldLanes ≤ h/2 ∧
    ((s).high+(s).low)*((s).high+(s).low) ≤ h/2 ∧ ((s).precision+(s).precision)*2^(s).low ≤ h/2 ∧
    DescentGLPacked.BankImage.SignedFields.joinWidth (s).precision (s).blocks*(s).gatherLanes ≤ h/2 ∧
    (s).flagWidth ≤ h/2 ∧ (v).venue.census.width ≤ h/2 := by
  have inv := PhysicalReset.selected_inventory G S board k tb i p f g drift degree h raw M C packet argLanes roleLanes printed old io.wire io.roster floor
  have seedFits := rootRoom
  rw [inventoryWidth inv.1 inv.2.1] at seedFits
  have rootFit (x : ℕ) (mem : x∈(v).rootUnits) : x*2^e ≤ h/2 := by
    have good := PhysicalReset.selected_room G S board k tb i p f g drift degree h raw M C packet argLanes roleLanes printed
      old io.wire io.roster floor x seedFits (.inl mem)
    rw [inv.2.2.1] at good
    exact good
  have cut:=PhysicalReset.selected_cut G S board k tb i p f g drift degree h raw M C packet argLanes roleLanes printed old
  have below:e ≤ cc:=by
    have nextWidth:=ResetOutput.next_difference S k tb i live
    have later:=cut.2.2
    omega
  have exactDim:cc-e+(e+k)=cc+k:=by omega
  have bits:0 < b:=by unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
  have paid:S.censusBits p ≤ 2*b:=by unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
  have prev:1*2^raw ≤ h/4:=quarter_key (m:=cc+k) bits localRoom (by omega) (Nat.sub_le ..)
  have amount:=quarter_key (m:=cc+k) bits localRoom paid (Nat.sub_le (laneBits (cc+k) h b) k)
  have oldRoom:2^raw ≤ h:=by simp only [one_mul] at prev;omega
  have opened:2^e ≤ h:=(Nat.pow_le_pow_right (by decide) cut.1).trans oldRoom
  have reshape:cc-e+(e+k)-cc=k:=by omega
  have members := fundingMembers (v)
  have paint:=rootFit ((s).precision*2^(v).middle.rootDepth+(s).precision) members.1
  have shuffle:=rootFit (((s).precision+(s).precision)*2^(v).middle.rootDepth) members.2.1
  have signal:=rootFit ((v).middle.signedBits*2^(v).middle.rootDepth) members.2.2.1
  refine ⟨by change old.lanes ≤ h; rwa [pitch],opened,?_,?_,?_,?_,?_,
    rootFit (v).venue.census.broadcast members.2.2.2⟩
  · change old.paidBits*old.lanes ≤ h/2
    rw [precision,pitch]
    exact amount.trans (by omega)
  · change (cc-e+(e+k))*(cc-e+(e+k)) ≤ h/2
    exact (congrArg₂ Nat.mul exactDim exactDim).le.trans dim
  · change (old.paidBits+old.paidBits)*2^(e+k) ≤ h/2
    change ((old.paidBits+old.paidBits)*2^k)*2^e ≤ h/2 at shuffle
    exact ((congrArg (fun x => (old.paidBits+old.paidBits)*x) (pow_add 2 e k)).trans
      ((Nat.mul_assoc _ _ _).symm.trans (Nat.mul_right_comm _ _ _))).le.trans shuffle
  · change (old.paidBits*2^old.k+old.paidBits)*2^e ≤ h/2
    change (old.paidBits*2^k+old.paidBits)*2^e ≤ h/2 at paint
    rw [blocks]
    exact paint
  · change (DescentSignedCableCodec.width old.degree old.cap*2^(cc-e+(e+k)-cc))*2^e ≤ h/2
    rw [reshape,capacity]
    exact signal

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
