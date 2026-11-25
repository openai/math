import OAI.Hierarchy.DescentFundedClipChoice
import OAI.Hierarchy.DescentOrdinaryVenueIngressPrice

namespace OAI
/-! # The ordinary ingress fee at the two live incoming packing widths -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPackedColony DescentRawCablePanel DescentOrdinaryVenueIngress
open DescentPacking.PackedMatch.Local ProtocolRAM

noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (extra : ℕ)
local notation "c₀" => v.fundedClip extra

/-- The old material panel can have a different pitch from the old actor bank. -/
theorem funded_input_width («matching» : 2^v.area.k+1≤v.area.unit) :
    ((c₀).peerBits+1)*(c₀).panelPitch≤v.payload/2 ∧ ((c₀).actorBits+1)*(c₀).actorPitch≤v.payload/2:=by
  have covered : 2*DepotRAM.totalBits (v.ticket.depotShape v.short)+1≤v.fundedPanelUnit:=
    (le_max_right ..).trans (le_max_right ..)
  have one:=lanes_fit v.payload v.fundedPanelUnit
  have two:=lanes_fit v.payload v.area.unit
  constructor
  · change (DepotRAM.totalBits (v.ticket.depotShape v.short)+1)*lanes v.payload v.fundedPanelUnit≤_
    rw [Nat.mul_comm];exact (Nat.mul_le_mul_left _ (by omega)).trans one
  · change (1*(2^v.area.k)+1)*lanes v.payload v.area.unit≤_
    rw [one_mul,Nat.mul_comm];exact (Nat.mul_le_mul_left _ «matching»).trans two

theorem funded_ingress_price («matching» : 2^v.area.k+1≤v.area.unit)
    (inputs : Inputs) (base w : ℕ) (panel : (c₀).radix≤(c₀).panelPitch)
    (actors : (c₀).radix≤(c₀).actorPitch) (space : 4*(c₀).unit*(c₀).radix≤v.payload):
    Clip.fee ((c₀).phase inputs base w)≤(c₀).factor*(c₀).mass:=by
  have r : 0<(c₀).radix:=Nat.two_pow_pos _
  obtain ⟨old,act⟩:=v.funded_input_width extra «matching»
  exact (c₀).tariff inputs base w (r.trans_le actors) (r.trans_le panel) ((c₀).working_pos panel actors space) old act

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
