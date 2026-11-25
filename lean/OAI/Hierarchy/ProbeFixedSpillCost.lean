import OAI.Hierarchy.ProbeFixedOriginalPrice
import OAI.Hierarchy.ProbeCoreWalks
import OAI.Hierarchy.ProtocolRAMCalendarRouteBox

namespace OAI
/-! # Pricing the row-major ordinary spill paths at the actual original catalogue addresses -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open AdaptiveProbe ProbeStage ProbeStage.Native ReportSockets CoreBoard
open scoped Classical
variable {S : PurchaseSampler} {z W k depth dates lines : ℕ}
    (π : Equiv.Perm (Fin (2^z))) (marks : Marks z W k dates)
    (ord : Catalogue S π depth marks ↪ Fin lines) (M : ℕ)

/-- Traversing an original core edge always displays its own length, even if
the same edge occurs in other retained, restored, or residual walks. -/
theorem core_spill_cost (i : Commodity (Fin (2^z)) (Stages z (2^W)) k) :
    (((commodityWalk (S:=S) π i).map (fun e=>ord (.inl e))).map (extendedLength ord (lenCode S π depth marks M))).sum=
      routeCap (Stages z (2^W)) M (PurchaseInventory.lane i) := by
  have ids (e : Edges S z (2^W) k) :
      extendedLength ord (lenCode S π depth marks M) (ord (.inl e))=coreLength (freeLength M) e := by
    exact (extendedLength_apply ord _ (.inl e)).trans (coreCode_read S M e)
  simp only [List.map_map,Function.comp_def,ids]
  exact ((commodity_walk (S:=S) π (fun _=>0 : Site z (2^W) k→Fin 1) M i).2).trans (routeCap_named z (2^W) k M i).symm

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
