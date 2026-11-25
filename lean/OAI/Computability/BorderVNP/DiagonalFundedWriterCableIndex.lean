import OAI.Computability.BorderVNP.PackedReportCableTransport

/-! # Cable indices in the funded writer's native table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical

/-- Casting the entire cable-name table agrees with reindexing each named edge. -/
theorem fundedCableCast_eq {m m' : ℕ} {E : Type*} (same : m = m') (edges : E ↪ Fin m) :
    cast (congrArg (fun count => E ↪ Fin count) same) edges =
      edges.trans (finCongr same).toEmbedding := by
  subst m'
  rfl

/-- The edge in a reindexed cable rectangle has its original numerical name. -/
theorem fundedCableName_val {m m' : ℕ} {E : Type*} (same : m = m')
    (edges : E ↪ Fin m) (e : E) :
    ((edges.trans (finCongr same).toEmbedding) e).val = (edges e).val := rfl

/-- The native geometry, cell numbers, wire bound and routing image use the
same cells and ports when the planner reindexes the cable rows. -/
theorem fundedWriterCableIndex {D s m m' n C d k b J A : ℕ}
    {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ} {N : Network D P bits}
    {cell : N.Site → Fin C} {aux : N.Site → ℕ} {sites : N.Site ↪ Fin s}
    {edges : N.Edge ↪ Fin m} {ports : P ↪ Fin n} {F : Fields s m n C d k b σ}
    {x : σ → Bool} {old : Fin J → Fin s} {live : Fin A → Fin n} {origin : ℕ} {ram : ℕ → ℕ}
    (same : m = m') (net : Represents N cell aux sites edges ports F x)
    (ids : ∀ c, (F.cells c).val = c.val)
    (width : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^b)
    (image : Image F old live x origin ram) :
    let fields := cast (congrArg (fun count => Fields s count n C d k b σ) same) F
    Represents N cell aux sites (edges.trans (finCongr same).toEmbedding) ports fields x ∧
      (∀ c, (fields.cells c).val = c.val) ∧
      (∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^b) ∧
      Image fields old live x origin ram := by
  subst m'
  exact ⟨net, ids, width, image⟩

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
