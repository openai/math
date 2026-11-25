import OAI.Hierarchy.DescentOperandPathBill
import OAI.Hierarchy.DescentDatedOperandOriginalHeads
import OAI.Hierarchy.DescentPhysicalSignedLayout

namespace OAI
/-! # The shared four-hop path and rank headers on an actual date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedSourcePathDirectory DescentDatedAddressBook DescentSIMDLookup
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)

theorem operand_path_charge (floor w ratio : ℕ) (signed : v.signed=v.signedLayout.format v.payload)
    (room : 2*v.signedLayout.unit≤ v.payload) (bus : w≤ ratio*v.payload) :
    let e:=v.material
    let D:=(v.ticket.depotShape v.short).degree
    (v.operandPaths floor w).wordInvoice+(v.operandRankPhase floor w).wordInvoice≤
      pathCharge e.oldHosts e.groups D v.payload (4*v.signedLayout.unit) ratio+
      rankCost e.oldHosts D v.payload ratio :=by
  intro e D
  have cap : e.lanes≤ v.payload:=by
    change v.signed.lanes≤ v.payload
    rw [signed];exact Nat.div_le_self ..
  have fill : v.payload≤ e.lanes*(4*v.signedLayout.unit):=by
    change v.payload≤ v.signed.lanes*(4*v.signedLayout.unit)
    rw [signed]
    change v.payload≤lanes v.payload v.signedLayout.unit*(4*v.signedLayout.unit)
    exact (occupancy _ _ v.signedLayout.positive room).2.trans_eq (by ring)
  exact Nat.add_le_add
    (all_word_bill _ (v.operandPathStart floor) e.oldHosts e.groups e.lanes D w v.payload
      (4*v.signedLayout.unit) ratio cap fill bus)
    (local_word_bill _ (v.operandRankStart floor) e.oldHosts D w v.payload ratio bus)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
