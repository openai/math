import OAI.Computability.BorderVNP.PackedSewnTileItemFits
import OAI.Computability.BorderVNP.PackedSewnFragmentOwners

/-! # Each enabled retained-port fragment belongs to a real old site -/

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
include hV in
private theorem tile_room : r*(2*w₀+R*link) ≤ V*g := gridRoom G hV
local notation "room" => tile_room G hV
local notation "out" => Network.packExternal (Bundle.layout (BlockHosts.bundle h)) (fun _ : FreeBlock R V => g) (BlockHosts.groupOwner (N := FineView.layout N lane) (V := V) h)
local notation "tm" => teamBlocks groups copies count
local notation "params" => (⟨R,r,w₀,link,g,V⟩ : FieldExport.Params)
variable (oldEdge : N.Edge ↪ Fin old) (oldPort : (Fin groups × Fin V) ↪ Fin (groups*V))
local notation "edge" => FieldExport.mergedEdges params (⟨hg,small,room⟩ : (params).Valid) oldEdge
local notation "port" => (finProdFinEquiv : FreeBlock R V ≃ Fin ((R+1)*V)).toEmbedding

variable {σ : Type*} {W : ℕ} (f : Inputs σ (groups*V) (old+4*(R+1)*V) ((R+1)*V) W)
    (x : σ → Bool) (owner : N.Site → ℕ)

variable [Fintype σ]
local notation "y" => (frame f (slot count old hg small room)).eval x

/-- Decode the copy, tile and six-slot address of each active old port operand. Its
assigned site is the attachment of that original tile, including linked and clamped lanes. -/
theorem tile_owners (cols : TileColumns G hV count N h hg small oldEdge oldPort f x owner)
    (oldFit : ∀ v, incoming N v < 2^W) (newFit : ∀ v, incoming out v < 2^W) :
    ∀ p ∈ Fragment.list y, ∃ v, p.site = owner v := by
  intro p hp
  obtain ⟨j,live,rfl⟩ := Fragment.exists_slot_of_mem hp
  obtain ⟨⟨team,tile,j⟩,rfl⟩ := (ordinal R V).surjective j
  obtain ⟨⟨group,i⟩,rfl⟩ := (tm).symm.surjective team
  let v := N.attach (group,tile)
  let a : Attached N v := ⟨(group,tile),rfl⟩
  let key := ordinal R V ((tm).symm (group,i),tile,j)
  let runs := TileRuns.runs (r:=r) (w:=w₀) ((tm).symm (group,i)) tile.val hg small
  let operand := item count ((tm).symm (group,i)) tile old hg small room
  let read (a : Fin (R+1) × Fin V × Fin 6) :=
    ((TileRuns.runs (r:=r) (w:=w₀) a.1 a.2.1.val hg small)[a.2.2.val]?).map (item count a.1 a.2.1 old hg small room)
  have sl : slot count old hg small room key = runs[j.val]?.map operand :=
    congrArg read ((ordinal R V).symm_apply_apply ((tm).symm (group,i),tile,j))
  have enabled := (active_iff f (slot count old hg small room) x key).mp live
  obtain ⟨row,hit,positive⟩ := enabled
  rw [sl] at hit
  cases get : runs[j.val]? with
  | none => simp [get] at hit
  | some q =>
    have eq : operand q = row := by simpa [get] using hit
    subst row
    change 0 < q.width at positive
    have fit := tileItem_fits G hV count N h hg small oldEdge oldPort f x owner v a i cols q positive (oldFit v) (newFit v)
    have read := (parse_eq f (slot count old hg small room) x (by rw [sl,get]; rfl) fit).trans
      (tileItem_parsed G hV count N h hg small oldEdge oldPort f x owner v a i cols q positive)
    exact ⟨v,congrArg Fragment.Parsed.site read⟩

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
