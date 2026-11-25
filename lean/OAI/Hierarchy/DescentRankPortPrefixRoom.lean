import OAI.Hierarchy.DescentPhysicalRankPortPhase
import OAI.Hierarchy.DescentPhysicalResetMixedSources

namespace OAI
/-! # Space for the four compact rank ports from the earlier actor and peer directories -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentPackedColony DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
noncomputable section
set_option quotPrecheck false
variable (v : ResetOutput) (base : ℕ)
local notation "A" => v.actor.directory (v.middle.stop base)
local notation "before" => v.candidateEnd base
local notation "end_" => v.rankPortEnd base
local notation "B" => v.rankPortRegs base

theorem ranked_space_earlier : v.actorEnd base≤v.massEnd base ∧ v.massEnd base≤before ∧
    end_≤v.finalEnd base:=by
  refine ⟨?_,?_,?_⟩
  · unfold massEnd trunkEnd
    rw [v.contactShape.translate,v.front.trunk_shift]
    omega
  · have cut:=v.receipt_order base
    apply le_trans _ (v.sheets.room (v.remap base).endAddress)
    change v.massEnd base≤v.privateEnd base+(v.remap base).size
    omega
  · have earlier:=v.earlier base
    have up : end_≤v.ticketEnd base:=by
      exact (((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)).trans
        (Nat.le_add_right ..)
    exact up.trans ((earlier.2.1.trans earlier.2.2).trans (v.final_ge base))

private theorem lift_fits {bank : Bank} {cut limit w : ℕ} (le : cut≤limit) (fit : bank.Fits w cut) :
    bank.Fits w limit:=⟨fit.1,fit.2.1,fit.2.2.trans le⟩

/-- Every source bank is complete before the next rank copy. On the named
calendar, the old sparse canvas is the full actor directory by construction. -/
theorem rank_port_room {w : ℕ} (old : v.OriginalOperands base) (joint : v.JointRoom base old w)
    (same : v.front.peer.hosts≤(A).sites) (endRoom : v.finalEnd base<2^w) : v.RankPortRoom base w:=by
  obtain ⟨previous,issued,high⟩:=v.ranked_space_earlier base
  have limit:=high.trans_lt endRoom
  have original:=(v.rankPort_after base).trans_lt limit
  have values : (A).ranks.base+(A).ranks.size≤(A).endAddress:=by
    change (A).first+2*(A).pitch+(A).pitch≤(A).first+(4*(A).pitch+1+4*(A).sites)
    omega
  have source : (A).ranks.Fits w before:=by
    have low:=values.trans (previous.trans issued)
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (low.trans_lt original),low⟩
  have typed : v.front.peer.hosts≤(B).forward.size:=
    same.trans (Nat.le_pow_clog (by decide) (A).sites)
  have roof : DescentRankPortRoster.roof before v.sheets.hosts≤end_:=by
    unfold rankPortEnd DescentRankPortChart.endAddress DescentScalarHaloPortROM.stop
    change DescentRankPortRoster.roof before v.sheets.hosts≤DescentRankPortRoster.roof before v.sheets.hosts+_+_
    omega
  exact ⟨⟨lift_fits issued joint.measured.count,lift_fits issued joint.measured.inverse,source,
    lift_fits issued joint.measured.current,typed,by simpa only [jointRegisters,rankPortRegs,Nat.mul_comm] using joint.measured.four,
    roof.trans_lt limit⟩,limit⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
