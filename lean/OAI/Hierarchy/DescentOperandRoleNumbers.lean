import OAI.Hierarchy.DescentGadgetRolePorts

namespace OAI
namespace Hierarchy.DescentOperandPhysicalInput
open DescentKernelHistory
noncomputable section

inductive Role where | original (slot : Fin 2) | arm (slot : Fin 2) | supply (slot : Fin 8)

def role {j : Fin 6} : RolePort j→Role
  | .inl (.inl s)=>.original s.val
  | .inl (.inr s)=>.arm s.val
  | .inr (.inl s) | .inr (.inr s)=>.supply s.val

def Role.kind : Role→ℕ | .original _=>0 | .arm _=>1 | .supply _=>2
def Role.slot : Role→ℕ | .original i | .arm i=>i.val | .supply i=>i.val

def roleAt (j : Fin 6) (a : Fin (Fintype.card (RolePort j))) := role ((roleIndex j).symm a)

end
end Hierarchy.DescentOperandPhysicalInput

end OAI
