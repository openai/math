import OAI.Computability.BorderVNP.PackedSewnTileItemFits
import OAI.Computability.BorderVNP.PackedSewnTileViews
import OAI.Computability.BorderVNP.PackedSewnTileColumnReads

/-! # Actual old and new singleton-site columns of the sewn tile candidate -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Grid

open Crossing Inherited TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open Fragment.Tile CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option quotPrecheck false

variable {D R r t pins link inner n V groups copies old : ℕ} {E : Type}
    (G : Wiring R r t pins link inner n E) (hV : 0 < V) (count : groups*copies = R+1)
    (N : Network D (Fin groups × Fin V) (fun _ => copies*blockWidth (r*n) V))
    (h : BlockHosts (FineView.layout N (groupedLane G V hV groups copies count))
      (Equiv.refl (PublicPort R r (G.program.length+t) link)) (blockWidth (r*n) V))
    (hg : 0 < blockWidth (r*n) V) (small : blockWidth (r*n) V ≤ link)
local notation "g" => blockWidth (r*n) V
local notation "w₀" => G.program.length+t
local notation "lane" => groupedLane G V hV groups copies count
open private tile_room from OAI.Computability.BorderVNP.PackedSewnTileSemantic
local notation "room" => tile_room G hV
local notation "out" => Network.packExternal (Bundle.layout (BlockHosts.bundle h)) (fun _ : FreeBlock R V => g) (BlockHosts.groupOwner (N := FineView.layout N lane) (V := V) h)
local notation "tm" => teamBlocks groups copies count
local notation "params" => (⟨R,r,w₀,link,g,V⟩ : FieldExport.Params)
variable (oldEdge : N.Edge ↪ Fin old) (oldPort : (Fin groups × Fin V) ↪ Fin (groups*V))
local notation "edge" => FieldExport.mergedEdges params (⟨hg,small,room⟩ : (params).Valid) oldEdge
local notation "port" => (finProdFinEquiv : FreeBlock R V ≃ Fin ((R+1)*V)).toEmbedding

variable {γ σ τ : Type*} [Fintype γ] [Fintype σ] [Fintype τ] {s C C' d d' k k' W : ℕ}
    (F : Fields s old (groups*V) C d k W σ)
    (B : Fields s (old+4*(R+1)*V) ((R+1)*V) C' d' k' W τ)
    (oldPin : σ → γ) (newPin : τ → γ) (hd : d ≤ W) (zero : γ) (x : γ → Bool)
    (oldName : N.Site ↪ Fin s) (newName : N.Site ↪ Fin s)
local notation "z" => (physicalBase F B oldPin newPin).eval x
local notation "fields" => physicalFields (m := old+4*(R+1)*V) (n := (R+1)*V) F oldPin hd zero
local notation "siteCode" => fun v => (F.sites (oldName v)).val

/-- Both singleton-cell scans and the old port pointer implement all columns used by the scalar fragment proof. -/
theorem TileColumns.of_physical (hz : x zero = false)
    (rowMajor : ∀ p, oldPort p = finProdFinEquiv p)
    (before : Views.EndpointData N F oldName oldEdge oldPort (x ∘ oldPin))
    (after : Views.EndpointData out B newName edge port (x ∘ newPin))
    (oldRoom : ∀ v, incoming N v < 2^W) (newRoom : ∀ v, incoming out v < 2^W) :
    TileColumns G hV count N h hg small oldEdge oldPort fields z siteCode := by
  constructor
  · intro p
    rw [physical_owner F B oldPin newPin hd zero x hz,← rowMajor p]
    exact before.attach p
  · intro v a
    rw [physical_oldStart F B oldPin newPin hd zero x,← rowMajor a.val]
    exact Views.attached_value N F oldName oldEdge oldPort before oldRoom v a
  · intro v a
    rw [physical_newStart F B oldPin newPin hd zero x]
    exact Views.attached_value out B newName edge port after newRoom v a
  · intro c
    rw [physical_newStart F B oldPin newPin hd zero x]
    exact Views.source_from_endpoints out B newName edge port after newRoom (.inr c)
  · intro c
    rw [physical_newStart F B oldPin newPin hd zero x]
    exact Views.dest_from_endpoints out B newName edge port after newRoom (.inr c)

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
