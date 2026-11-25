import OAI.Hierarchy.DescentSiteNameRead
import OAI.Hierarchy.DescentReached

namespace OAI
/-! # Read the physical names of the actual source of a selected ordinary date -/
namespace Hierarchy.DescentSixParty.Reached
open GroupStage DescentPacking DescentStageEdgeReceipt
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist : ℕ} {W : MarkedWorld F d P bits}
variable (R : Reached W G q ε S k i z D wire hist)
local notation "rank" => groupRank Fin.valEmbedding (R.vertex.trans Fin.valEmbedding)

/-- A named source has the exact native site order demanded by the measured-donor decoder.
This applies equally to a named input raster and to every physically renamed successor. -/
theorem donor_site_named (spec : ∀v,originalId W.graph.Site v=(R.placement.site R.vertex R.valid.coordinates v).val) :
    R.placement.SiteNamed rank := R.placement.siteNamed_of_read R.vertex R.valid.coordinates spec

theorem donor_names (old : 0 < i) :
    R.placement.SiteNamed rank ∧ ∀e f,(R.order e).val<(R.order f).val ↔ originalId W.graph.Edge e<originalId W.graph.Edge f :=
  ⟨R.donor_site_named (R.siteName old),fun e f=>by rw [R.edgeName old e,R.edgeName old f]⟩


end
end Hierarchy.DescentSixParty.Reached

end OAI
