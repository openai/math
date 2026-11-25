import OAI.Hierarchy.DescentSeedSiteGeometry
import OAI.Hierarchy.DescentDatedSeedLayout
import OAI.Hierarchy.DescentDatedNodeMetadataChart

namespace OAI
/-! The two original packed metadata pages and the true arity at a physical host. -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentPackedSeed DescentSeedRoot DescentSeedInitialTable Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp p H : ℕ} (X : Approximation F cp p)
    (publicWide : Fintype.card (Vertex X) ≤ H) (l : Layout)
def nodeChart (l : Layout) (d H G : ℕ) : DescentDatedNodeMetadata.Chart :=
  ⟨2^d,1,H,G,l.operandBits,l.operandLanes⟩

def nodeArities (h : Fin H) : Option ℕ :=
  (rack X ((Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)) h).map (fun v=>legArity X v*l.groupsPerNode)

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
