import OAI.Computability.BorderVNP.PackedHistoryPrivateSites

/-! # Cable and port names carried by the private-program replay

Each state has the physical row names read by its successor. The child's
rectangular cable index is the one sorted by the public stage, and the
attained successor carries the sparse row IDs of the stage's second save.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Program

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicParallel Packing Epoch.Round
open scoped Classical
attribute [local instance] portFintype

variable {D m k b : ℕ} [NeZero D] {I P K : Type} [Fintype I] [Fintype P] [Field K]
  {bits : P → ℕ} {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
  {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
  (F : Program (B := B) e view) (store : F.SaveNames) (directory : F.SiteRows)

/-- Actual capacity and sparse row witnesses of a coherent private-site traversal. -/
structure SiteModelRows where
  /-- Rectangular cable capacity at each level of the saved program. -/
  capacity : ℕ → ℕ
  /-- Cable identifiers actually used in each attained state. -/
  edges : ∀ n (x : A n), (view n x).pack.layout.Edge ↪ Fin (capacity n)
  /-- The parallel rectangle has one block for every selected child. -/
  inputCap : ∀ i c, (F.stage i c).rowCount = k*capacity i.val
  /-- Public cable slots are the same parallel block-and-row indices as in the child models. -/
  inputRows : ∀ i c z, ((F.stage i c).slot z).val = (parallelName (fun j => edges i.val (c j)) z).val
  /-- The destination's rectangular capacity agrees with the dense-save receipt. -/
  savedCap : ∀ i c q, capacity (i.val+1) = store.capacity i c q
  /-- Public IDs on the saved state are the actual occupied sparse result cable IDs. -/
  savedRows : ∀ i c q, HEq (edges (i.val+1) (F.advance i c q))
    (CutCircuit.denseRows ((F.stage i c).result e q).pack.layout (store.number i c q))
  /-- Exterior port rows have the parallel copy-block capacity. -/
  portCap : ∀ i : Fin b, directory.nPort (i.val+1) = k*directory.nPort i.val
  /-- Each copy has its original exterior ports at the actual offset assigned to that copy. -/
  portRows : ∀ (i : Fin b) u, (directory.ports (i.val+1) u).val =
    (Inherited.Parallel.portRows k (directory.ports i.val) u).val

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
