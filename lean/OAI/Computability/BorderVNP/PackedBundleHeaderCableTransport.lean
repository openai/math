import OAI.Computability.BorderVNP.PackedReportCableTransport
import OAI.Computability.BorderVNP.PackedBundleGeometryHeaders

/-! # Transport of the sorted report headers to the allocated cable rectangle -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open CellAddressCircuit VPVNP.VerifierNetwork

variable {σ : Type*} [Fintype σ] {s m m' n C d k w J : ℕ}
    {F : Fields s m n C d k w σ}

/-- Reindexing the sparse cable rows preserves the full frame of original
report headers, including every operand supplied to the stable sorter. -/
theorem geometryHeaders_castCables (he : m = m') (old : Fin J → Fin s) (desc : ℕ)
    (cfg : Frame σ (Config C w)) (shape : Fin J → Shape) :
    geometryHeaders (F.castRect rfl he) old desc cfg shape = geometryHeaders F old desc cfg shape := by
  subst m'
  rfl

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI
