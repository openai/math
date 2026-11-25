import OAI.Computability.BorderVNP.PackedNamedEndpointTransport
import OAI.Computability.BorderVNP.PackedRoutingPrivateViews

/-! # Reindexing the issued report fields to the native cable rectangle

The geometry export counts the sewn cables in its own sparse array.  The signed
arena reserves that same number of cable rows.  Transport along this equality
preserves the branch representation and the absolute addresses of its output.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open Crossing CellAddressCircuit CellAddressPhysical VPVNP.VerifierNetwork

variable {s m m' n C d k w : ℕ} {σ : Type*} {F : Fields s m n C d k w σ}

/-- Transport of the cable rectangle preserves the entire embedding of cell codes. -/
@[simp] theorem CellAddressCircuit.Fields.castRect_cells (he : m = m') :
    (F.castRect rfl he).cells = F.cells := by
  subst m'
  rfl

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}
    {cell : N.Site → Fin C} {aux : N.Site → ℕ} {sites : N.Site ↪ Fin s}
    {edges : N.Edge ↪ Fin m} {ports : P ↪ Fin n} {x : σ → Bool}

/-- Every actual cable keeps its ordinal and the transported fields represent
the same sites, endpoints, widths and holes. -/
theorem CellAddressPhysical.Represents.castCables (he : m = m')
    (h : Represents N cell aux sites edges ports F x) :
    Represents N cell aux sites (edges.trans (finCongr he).toEmbedding) ports (F.castRect rfl he) x := by
  subst m'
  exact h

namespace RoutingOutputs

open VPVNP.BurstRAM GeometryFrameEncoding ParseBatchSort DiagonalResidueRAM

variable [Fintype σ] {J A o W : ℕ} {old : Fin J → Fin s} {live : Fin A → Fin n} {origin : ℕ}

/-- The issued word-addressed RAM image is also the image of the reindexed fields. -/
theorem Image.castCables (he : m = m') {mem : ℕ → ℕ} (h : Image F old live x origin mem) :
    Image (F.castRect rfl he) old live x origin mem := by
  subst m'
  exact h

/-- The report's private staging and internal-wire views form exactly the
same output frame after the cable rectangle is reindexed. -/
theorem castCables_withPrivateViews (he : m = m') (rest : Frame σ (Outputs o w)) :
    withPrivateViews (F.castRect rfl he) old rest = withPrivateViews F old rest := by
  subst m'
  rfl

/-- Reuse the word receipt of the geometry program at every appended output,
including the absolute offset past the original triples and routing arrays. -/
theorem castCables_privateWords (he : m = m') {mem : ℕ → Word W} {rest : Frame σ (Outputs o w)}
    (h : ∀ i : Fin ((C+(J+C))+o),
      mem (origin+m*3+count m C J A+i.val) =
        word W (value fun j => (withPrivateViews F old rest).eval x (.inl (i,j)))) :
    ∀ i : Fin ((C+(J+C))+o), mem (origin+m'*3+count m' C J A+i.val) =
      word W (value fun j => (withPrivateViews (F.castRect rfl he) old rest).eval x (.inl (i,j))) := by
  subst m'
  exact h

end RoutingOutputs

end Packing

end BorderVNP
end Computability
end OAI
