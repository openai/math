import OAI.Hierarchy.DescentSeedWorldNames
import OAI.Hierarchy.DescentResidentDonorNames

namespace OAI
/-! # Start the first nonlinear ordinary choice on the numbered physical seed graph

Both permutations are proof-level changes of network coordinates. Mutable registers continue to
use the old physical host, block and cable ordinals. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentPacking DescentStageEdgeReceipt DescentPhysicalOrder
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist : ℕ}
    (R : Reached W G q ε S k i z D wire hist)
local notation "A" => R.placement

theorem named :
    (placed R).SiteNamed (groupRank Fin.valEmbedding (R.vertex.trans Fin.valEmbedding)) ∧
    ∀e f,((reached R).order e).val<((reached R).order f).val ↔
      originalId (world R).graph.Edge e<originalId (world R).graph.Edge f := by
  constructor
  · apply (reached R).donor_site_named
    intro t;obtain ⟨u,rfl⟩:=(site R).surjective t
    exact (site_code R u).trans (site_at R u).symm
  · intro e f;obtain ⟨a,rfl⟩:=(edge R).surjective e;obtain ⟨b,rfl⟩:=(edge R).surjective f
    rw [edge_code,edge_code]
    change R.order ((edge R).symm ((edge R) a)) < R.order ((edge R).symm ((edge R) b)) ↔
      R.order a < R.order b
    simp only [Equiv.symm_apply_apply]

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
