import OAI.Hierarchy.DescentRegisteredOperandSource
import OAI.Hierarchy.DescentDatedOperandRun

namespace OAI
/-! # The prior pointer and its four numerical fields from the same operand books -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandStateBanks
open DescentPackedColony DescentPackedOperand ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {l : Layout} {w : ℕ}
theorem registered_books (t : Banks l) (b : Books l) (typed : BookPointers b) (s route room) (m : Memory w)
    (previous : ∀x p,Reads (t.previous x p) (b x p) l.lanes m)
    (side : ∀j i,Reads (t.side j i) (fun h g=>sourceFields ((ofBooks b typed s route room j).fragment h g)
      (DescentPriorOperandColumns.sideIndex i)) l.lanes m)
    (roles : ∀j i,Reads (t.route j i) (route j i) l.lanes m) :
    t.Registered (ofBooks b typed s route room) m:=
  ⟨fun j p=>previous (l.index.symm j).1 p,fun j f h g=>ofBooks_header b typed s route room j h g f,side,roles⟩

end
end Hierarchy.DescentDatedPriorOperand

end OAI
