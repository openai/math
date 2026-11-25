import OAI.Computability.BorderVNP.PackedReportCableTransport

/-! # Reading original host geometry through the planner's cable rectangle -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open Crossing CellAddressCircuit CellAddressPhysical VPVNP.VerifierNetwork

variable {s m m' n C d k w : ℕ} {σ : Type*} {F : Fields s m n C d k w σ}
    {D : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits} {cell : N.Site → Fin C}
    {aux : N.Site → ℕ} {sites : N.Site ↪ Fin s} {edges : N.Edge ↪ Fin m} {ports : P ↪ Fin n}
    {x : σ → Bool}

/-- A native table represented after the checked cable reindexing still
represents the same original sparse identifiers. -/
theorem CellAddressPhysical.Represents.of_castCables (same : m=m')
    (h : Represents N cell aux sites (edges.trans (finCongr same).toEmbedding) ports (F.castRect rfl same) x) :
    Represents N cell aux sites edges ports F x := by
  subst m'
  exact h

namespace RoutingOutputs

open VPVNP.BurstRAM GeometryFrameEncoding ParseBatchSort DiagonalResidueRAM

/-- The complete physical geometry image before the canonical placement is
also the image of the original network rectangle. -/
theorem Image.of_castCables [Fintype σ] (same : m=m') {J A : ℕ} {old : Fin J → Fin s}
    {live : Fin A → Fin n} {origin : ℕ} {mem : ℕ → ℕ}
    (h : Image (F.castRect rfl same) old live x origin mem) : Image F old live x origin mem := by
  subst m'
  exact h

end RoutingOutputs
end Packing

end BorderVNP
end Computability
end OAI
