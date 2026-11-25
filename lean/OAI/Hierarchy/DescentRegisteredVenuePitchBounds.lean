import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentNamedOrdinaryVenue

namespace OAI
/-! # Width of the two ordinary successor buses at the issued clipped pitch -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentOrdinaryVenueIngress DescentPacking.PackedMatch.Local.Stage
noncomputable section

theorem fundedClipAt_paid_pitch (a : Dated.Ordinary) (socket : DescentRawCablePanel.DepotRAM.Shape)
    (donor paid extra : ℕ) :
    let c:=fundedClipAt a socket donor paid extra
    c.postPitch ≤ a.payload ∧ paid*c.postPitch ≤ a.payload/4 := by
  intro c
  have live : 0<c.radix:=Nat.two_pow_pos _
  have below : c.postPitch≤c.working:=Nat.le_mul_of_pos_right _ live
  have room : paid≤fundedUnitAt a paid := (Nat.le_add_left ..).trans (Nat.le_max_left ..)
  have full : paid≤c.unit:=room.trans ((Nat.le_max_left ..).trans (Nat.le_max_right ..))
  have cap : c.working*c.unit≤a.payload/4:=c.working_fields.2.2
  have actor : c.panelPitch≤a.payload:=Nat.div_le_self ..
  exact ⟨below.trans (c.working_fields.1.trans actor),
    (Nat.mul_le_mul full below).trans (by simpa only [Nat.mul_comm c.unit] using cap)⟩

variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (book : OrdinaryBooks) (ticket : OrdinaryLink prevWorld he T choice n next)
    (gain tail p f payload seats hostLanes : ℕ) (old : ProtocolRAM.Bank) (orig : ℕ→Dated.Ordinary)
    (ports : DatePorts) (floor : ℕ)
local notation "v" => book.onTicket ticket gain tail p f payload seats hostLanes old orig
set_option quotPrecheck false in
local notation "pitch" => ((v).fundedClip ((v).argumentUnitFrom ports floor)).postPitch

theorem registered_venue_pitch :
    ((v).registeredFrom ports floor).venue=StageVenueTail.Date.atOrdinary G S gain k tail p f payload orig i pitch ∧
    pitch≤payload ∧ S.censusBits p*pitch≤payload/4 :=
  ⟨rfl,fundedClipAt_paid_pitch (v).area ((v).ticket.depotShape (v).short) (v).fundedPanelUnit
    (S.censusBits p) ((v).argumentUnitFrom ports floor)⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
