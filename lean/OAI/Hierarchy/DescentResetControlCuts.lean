import OAI.Hierarchy.DescentResetPublicCuts

namespace OAI
/-! # Physical actor, roster and operand address bounds for the control scan -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
noncomputable section

/-- The control registers follow both actor publication and the full physical
four-word roster for each host. Their last word precedes the operand arena. -/
theorem control_address_bounds (v : ResetOutput) (b : ℕ) :
    v.actorEnd b ≤ v.controlFloor b ∧ v.sheets.hosts ≤ v.controlFloor b ∧
    v.controlFloor b ≤ v.operandFloor b ∧ v.operandFloor b ≤ v.finalEnd b := by
  obtain ⟨_,_,trunk,mass,joint,priv,«meta»,orig,canon,_,_⟩ := v.cuts b
  have actor : v.actorEnd b ≤ v.candidateEnd b :=
    ((((((trunk.trans mass).trans joint).trans priv).trans «meta»).trans orig).trans canon)
  have pad : 4*v.sheets.hosts ≤ 2^(Nat.clog 2 (4*v.sheets.hosts)) :=
    Nat.le_pow_clog (by decide) _
  have host : v.sheets.hosts ≤ v.rankPortEnd b := by
    unfold rankPortEnd DescentRankPortChart.endAddress DescentRankPortChart.rosterEnd DescentScalarHaloPortROM.stop
    omega
  have ticket : v.rankPortEnd b ≤ v.ticketEnd b := by
    unfold ticketEnd pairEnd DescentResetSourceTicketPair.endAt
      DescentResetSourceTicketBank.endAddress DescentResetSourceTicketBank.start
    exact (((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans
      (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have mid : v.rankEnd b ≤ v.controlFloor b := by
    change v.rankEnd b ≤ DescentNextSignedWindow.Native.All.endAddress (v.fieldsEnd b) _ _ _ _ _ _
    unfold fieldsEnd DescentResetFieldAssembler.endAddress DescentNextSignedWindow.Native.All.endAddress
    omega
  have control : v.rankPortEnd b ≤ v.controlFloor b :=
    (ticket.trans (v.earlier b).2.1).trans mid
  have floor : v.controlFloor b ≤ v.operandFloor b := by
    change v.controlFloor b ≤ v.controlRegisters.endAddress (v.controlFloor b)
    rw [v.controlRegisters.translated]
    exact Nat.le_add_right ..
  have setup : v.operandFloor b ≤ v.keepBase b := by
    change v.operandFloor b ≤ v.setup.endAddress (v.operandFloor b)
    rw [v.setup.affine]
    exact Nat.le_add_right ..
  obtain ⟨installed,placed⟩ := v.operand_order b
  exact ⟨(actor.trans (v.rankPort_after b)).trans control,host.trans control,floor,
    (((setup.trans (Nat.le_add_right (v.keepBase b) v.keepWords)).trans installed).trans placed).trans (v.final_ge b)⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
