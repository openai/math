import OAI.Computability.BorderVNP.PackedRoutingImage

/-! # The routing image at the issued directory's destination -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open CellAddressCircuit

/-- Use the attained routing image at the issued destination after identifying
it with the report directory's destination. All rows, bits and RAM are retained. -/
theorem Image.atIssuedOrigin {s m n C d k w J A issued report : ℕ}
    {σ : Type*} [Fintype σ] {fields : Fields s m n C d k w σ}
    {old : Fin J → Fin s} {ports : Fin A → Fin n} {bits : σ → Bool} {ram : ℕ → ℕ}
    (image : Image fields old ports bits report ram) (same : issued = report) :
    Image fields old ports bits issued ram := by
  subst issued
  exact image

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
