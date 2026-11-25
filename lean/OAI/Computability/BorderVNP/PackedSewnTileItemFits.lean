import OAI.Computability.BorderVNP.PackedSewnTileSemantic

/-! # Address and width bounds of positive frozen tile operands -/

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

variable {σ : Type*} {W : ℕ} (f : Inputs σ (groups*V) (old+4*(R+1)*V) ((R+1)*V) W)
    (x : σ → Bool) (owner : N.Site → ℕ)

variable (v : N.Site) (a : Attached N v) (i : Fin copies)
local notation "u" => (tm).symm (a.val.1,i)
local notation "runspec" => TileRuns.Run R r w₀ link g u a.val.2.val
local notation "readAt" => copyRead G hV count N h hg oldEdge oldPort edge port v a i
local notation "fr" => fragment G hV count N h hg oldEdge oldPort edge port v a i
local notation "itemAt" => item count u a.val.2 old hg small room


/-- The enabled public operands fit the word width whenever the two true site inputs fit. -/
theorem tileItem_fits (cols : TileColumns G hV count N h hg small oldEdge oldPort f x owner)
    (q : runspec) (pos : 0 < q.width) (oldFit : incoming N v < 2^W) (newFit : incoming out v < 2^W) :
    f.Fits x (itemAt q) := by
  have team := (tm).apply_symm_apply (a.val.1,i)
  have oldSlot := cols.original v a
  have endOld := portEnd_le N oldEdge oldPort v a
  change portStart N oldEdge oldPort v a+copies*g ≤ incoming N v at endOld
  have nextCopy := Nat.mul_le_mul_right g (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at nextCopy
  have fit := q.fit
  have low : q.first < g := by omega
  have target := tile_source G hV count N h hg small oldEdge oldPort f x owner v a i cols q pos
  refine ⟨?_,?_,?_⟩
  · simp only [item,team,Prod.mk.eta,oldSlot]
    omega
  · change q.width < 2^W
    omega
  · intro e he
    rw [he,Option.map_some] at target
    change some _ = (if h : q.first<g then (readAt ⟨q.first,h⟩).map Fin.val else none) at target
    rw [dite_eq_left low] at target
    cases re : readAt ⟨q.first,low⟩ with
    | none => rw [re] at target; contradiction
    | some j =>
      rw [re,Option.map_some,Option.some.injEq] at target
      exact target ▸ j.isLt.trans newFit

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
