import OAI.Hierarchy.DescentDatedOperandRecordedSide
import OAI.Hierarchy.DescentOrdinaryRegisteredOperands
import OAI.Hierarchy.DescentDatedOperandDigits

namespace OAI
/-! Relating the six physical side fields to the original registered operand book. -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentPackedColony DescentOperandStateBanks DescentPackedOperand ProtocolRAM
open DescentPriorOperandColumns Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {l : Layout} {w : ℕ}

theorem registered_digits (t : Banks l) (b : Books l) (typed : BookPointers b) (s route room) (m : Memory w)
    (previous : ∀x p,Reads (t.previous x p) (b x p) l.lanes m)
    (fields : ∀j i,Reads (t.side j i) (fun h g=>(s j h g : Side l.size).digits i) l.lanes m)
    (roles : ∀j i,Reads (t.route j i) (route j i) l.lanes m) :
    t.Registered (ofBooks b typed s route room) m := by
  apply registered_books t b typed s route room m previous _ roles
  intro j i
  simpa only [Source.fragment,Side.side_value,ofBooks] using fields j i

end
end Hierarchy.DescentDatedPriorOperand

end OAI
