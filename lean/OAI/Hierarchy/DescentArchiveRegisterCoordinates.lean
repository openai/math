import OAI.Hierarchy.DescentRegisterTypes
import OAI.Hierarchy.DescentOriginalPaddedNodes
import OAI.Hierarchy.DescentDatedPriorOperand

namespace OAI
/-! # The physical bounds and row shape of an archived register -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentKernelHistory DescentCompiler DescentDatedPriorOperand
noncomputable section
def rangeLayout (ports : DatePorts) : Layout :=
  ⟨2^ports.venue.k,ports.nodes,ports.argumentsPerNode,ports.operandHosts,ports.venue.groups,
    ports.operandLanes,ports.operandBits-2⟩

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k wire hist w : ℕ}

/-- Size and placement bounds for addressing the physical register returned at this date. -/
structure RangeRoom {W : MarkedWorld F d P bits} {i z D : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k i z D wire hist) (B : BitDescription W) : Prop where
  capacity : ∀v,Fintype.card (B.recipe v).Node≤ports.nodes
  hosts : ∀v,(Reached.NodeCells.coordinate r v).1.val<ports.operandHosts
  groups : S.groupCount i=ports.venue.groups
  radix : k=ports.venue.k
  positive : 0<ports.operandLanes


end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
