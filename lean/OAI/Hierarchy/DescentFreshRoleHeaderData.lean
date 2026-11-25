import OAI.Hierarchy.DescentGadgetRolePorts
import OAI.Hierarchy.DescentSixPartyGadget
import OAI.Hierarchy.DescentBundleScalar

namespace OAI
/-! # The cardinality and interval table of an original fresh role -/
namespace Hierarchy.DescentFreshRoleFields
open DescentBundleHistory DescentSixParty DescentKernelHistory
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)
def width (z : ℕ) (a : Profile G.C) (j : Fin 6) : RolePort j→ℕ
  | .inl _=>z*G.b
  | .inr (.inl e)=>z*((a.1 e.val).val+G.k)
  | .inr (.inr e)=>z*((a.1 e.val).val+G.k)

def widths (z : ℕ) (a : Profile G.C) (j : Fin 6) :
    Fin (Fintype.card (RolePort j))→ℕ := width G z a j ∘ (roleIndex j).symm

def header (p z : ℕ) (a : Profile G.C) (j : Fin 6) :=
  List.ofFn (fun t=>List.replicate (widths G z a j t/p) (⟨0,1,1⟩ : SliceCode))

def arity (p z : ℕ) (a : Profile G.C) (j : Fin 6) := ∑t,widths G z a j t/p

end
end Hierarchy.DescentFreshRoleFields

end OAI
