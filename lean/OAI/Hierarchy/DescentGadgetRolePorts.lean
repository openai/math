import OAI.Hierarchy.DescentSixPartySeed

namespace OAI
/-! # Enumerating the actual demand and supply ports of each of the six parties -/
namespace Hierarchy.DescentKernelHistory
open DescentSixParty
open scoped Classical
noncomputable section

abbrev RolePort (j : Fin 6) :=
    ({s : Fin 2 // demandSrc s=j} ⊕ {s : Fin 2 // demandDst s=j}) ⊕
    ({s : Fin 8 // supplySrc s=j} ⊕ {s : Fin 8 // supplyDst s=j})

def roleIndex (j : Fin 6) : RolePort j ≃ Fin (Fintype.card (RolePort j)) := Fintype.equivFin _

end
end Hierarchy.DescentKernelHistory

end OAI
