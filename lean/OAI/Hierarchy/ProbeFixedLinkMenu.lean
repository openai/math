import OAI.Hierarchy.ProbeFixedFormatCore
import OAI.Hierarchy.ProbeReportedGeometry
import OAI.Hierarchy.TaggedWireLinearRoleRoom
import OAI.Hierarchy.ProtocolRAMCatalogueActiveBill

namespace OAI
/-! # Public positive-link stage, minimum price and density for shortening -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

theorem positive_metric {h attempts depth : ℕ} (π : Equiv.Perm (Fin (2^h))) (marks : Marks h v.W k attempts)
    (e : Catalogue v.sampler π depth marks) (paid : 0<scaleOf v.sampler π depth marks e) :
    scaleOf v.sampler π depth marks e=TaggedShorterBudget.dyadic v.W ∧
      lenCode v.sampler π depth marks v.radius e=1 ∧
      Λ*(scaleOf v.sampler π depth marks e)^σ≤(lenCode v.sampler π depth marks v.radius e:ℝ) := by
  rcases e with (f|w)|b
  · exact (lt_irrefl (0:ℝ) paid).elim
  · exact ⟨rfl,rfl,by simpa [scaleOf,lenCode,coreScale,coreCode] using v.geometry.length_floor⟩
  · exact ⟨rfl,rfl,by simpa [scaleOf,lenCode] using v.geometry.length_floor⟩

def rowFactor := CoreCatalogue.coreFactor v.sampler (2^v.W) k+
  HistoryRoles.RoleProgram.RoleRoom.boughtFactor (2^v.W) k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)
    v.sampler.degree (publicTiles k v.W-1)

theorem board_rows {h : ℕ} (b : Board) (order : Fin b.coreRows≃Edges v.sampler h (2^v.W) k)
    (sz : ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)*
      (PurchaseFrozen.count h (2^v.W) k*PurchaseFrozen.paths h v.sampler.degree (publicTiles k v.W-1))=b.boughtRows) :
    b.rows≤v.rowFactor*2^h := by
  change b.coreRows+b.boughtRows≤_
  rw [←sz]
  exact HistoryRoles.RoleProgram.RoleRoom.padded_edges v.sampler (publicTiles k v.W-1) order

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
