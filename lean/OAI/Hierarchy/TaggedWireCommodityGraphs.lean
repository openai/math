import OAI.Hierarchy.ProbeCoreWalkMount
import OAI.Hierarchy.TaggedWireGoodsDistinct

namespace OAI
/-! # The original endpoint pairs of every commodity and reserve row -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
variable {h d k K : ℕ}

def commodityGraph (π : Equiv.Perm (Fin (2^h))) (place : Site h d k → Fin K) :
    PortGraph (Fin K) (Commodity (Fin (2^h)) (Stages h d) k) :=
  ⟨fun i=>place (commodityEnds π i).1,fun i=>place (commodityEnds π i).2⟩

def catalystGraph (place : Site h d k → Fin K) : PortGraph (Fin K) (Columns h d × Fin k) :=
  ⟨fun c=>place (c.1,some (c.2,false)),fun c=>place (c.1,some (c.2,true))⟩

theorem commodityGraph_distinct (π : Equiv.Perm (Fin (2^h))) (place : Site h d k→Fin K)
    (injective : Function.Injective place) (i : Commodity (Fin (2^h)) (Stages h d) k) :
    (commodityGraph π place).tail i≠(commodityGraph π place).head i := injective.ne (goods_different π i)

theorem catalystGraph_distinct (place : Site h d k→Fin K) (injective : Function.Injective place) (c : Columns h d×Fin k) :
    (catalystGraph place).tail c≠(catalystGraph place).head c := injective.ne (by simp)

end Hierarchy.ProbeStage.CoreBoard

end
end OAI
