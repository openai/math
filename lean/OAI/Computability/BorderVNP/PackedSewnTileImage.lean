import OAI.Computability.BorderVNP.PackedSewnTileRoster
import OAI.Computability.BorderVNP.PackedSewnTileEnumeration
import OAI.Computability.BorderVNP.PackedSewnTilePhysicalSemantic
import OAI.Computability.BorderVNP.PackedSewnTileItemFits

/-! # Exact positive fragment list of each old physical port directory

The emitted tile frame reindexes real row-major team and tile slots into
the attached original ports at the requested site. Each copy retains all
its genuine affine ranges and omits its unused reservations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Grid

open Crossing Inherited TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open Fragment.Tile CellAddressCircuit VPVNP.VerifierNetwork
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 4500
set_option quotPrecheck false

variable {D R r t pins link inner n V groups copies old : ℕ} {E : Type}
    (G : Wiring R r t pins link inner n E) (hV : 0 < V) (count : groups*copies = R+1)
    (N : Network D (Fin groups × Fin V) (fun _ => copies*blockWidth (r*n) V))
    (h : BlockHosts (FineView.layout N (groupedLane G V hV groups copies count))
      (Equiv.refl (PublicPort R r (G.program.length+t) link)) (blockWidth (r*n) V))
    (hg : 0 < blockWidth (r*n) V) (small : blockWidth (r*n) V ≤ link)
local notation "g" => blockWidth (r*n) V
local notation "w₀" => G.program.length+t
open private tile_room from OAI.Computability.BorderVNP.PackedSewnTileSemantic
local notation "room" => tile_room G hV
local notation "tm" => teamBlocks groups copies count
local notation "params" => (⟨R,r,w₀,link,g,V⟩ : FieldExport.Params)
variable (oldEdge : N.Edge ↪ Fin old) (oldPort : (Fin groups × Fin V) ↪ Fin (groups*V))
local notation "edge" => FieldExport.mergedEdges params (⟨hg,small,room⟩ : (params).Valid) oldEdge
local notation "port" => (finProdFinEquiv : FreeBlock R V ≃ Fin ((R+1)*V)).toEmbedding

local notation "out" => Network.packExternal (Bundle.layout (BlockHosts.bundle h))
  (fun _ : FreeBlock R V => g) (BlockHosts.groupOwner
    (N := FineView.layout N (groupedLane G V hV groups copies count)) (V := V) h)

variable {σ : Type*} [Fintype σ] {w : ℕ} (f : Inputs σ (groups*V) (old+4*(R+1)*V) ((R+1)*V) w)
    (x : σ → Bool) (owner : N.Site ↪ ℕ)
local notation "copiesAt" => copyRoster G hV count N h hg oldEdge oldPort edge port
local notation "y" => (frame f (slot count old hg small room)).eval x

/-- On the real endpoint columns, the active rows at each physical site
are precisely its old grouped-port intervals after both ordinal shifts. -/
theorem tileFrame_siteRuns (cols : TileColumns G hV count N h hg small oldEdge oldPort f x owner)
    (oldRoom : ∀ v, incoming N v < 2^w) (newRoom : ∀ v, incoming out v < 2^w) (v : N.Site) :
    (Fragment.siteRuns (owner v) (Fragment.list y)).Perm
      ((Finset.univ.toList.flatMap (fun a : Attached N v =>
        (copyIntervals copies g (copiesAt v small a)).map (atOffset (portStart N oldEdge oldPort v a)))).filter
          (fun z => decide (0<z.width))) := by
  let emit (a : Attached N v) (i : Fin copies) :=
    (((copiesAt v small a i).map (atOffset (i.val*g))).map (atOffset (portStart N oldEdge oldPort v a))).filter
      (fun z => decide (0<z.width))
  rw [siteRuns_eq_pick]
  have same (a : Attached N v) (i : Fin copies) :
      (List.finRange 6).filterMap (fun j =>
        pick y (owner v) (ordinal R V ((tm).symm (a.val.1,i),a.val.2,j))) = emit a i := by
    have fits q pos := tileItem_fits G hV count N h hg small oldEdge oldPort f x owner v a i cols q pos
      (oldRoom v) (newRoom v)
    have got := tile_picks G hV count N h hg small oldEdge oldPort f x owner cols v a i fits (owner v)
    simpa only [ite_true,emit,copyRoster,List.map_map,Function.comp_def] using got
  have each (p : Fin groups × Fin V) (i : Fin copies) :
      (List.finRange 6).filterMap (fun j =>
        pick y (owner v) (ordinal R V ((tm).symm (p.1,i),p.2,j))) =
        if hh : N.attach p=v then emit ⟨p,hh⟩ i else [] := by
    split
    next eq => exact same ⟨p,eq⟩ i
    next diff =>
      let a : Attached N (N.attach p) := ⟨p,rfl⟩
      have fits q pos := tileItem_fits G hV count N h hg small oldEdge oldPort f x owner _ a i cols q pos
        (oldRoom _) (newRoom _)
      have got := tile_picks G hV count N h hg small oldEdge oldPort f x owner cols _ a i fits (owner v)
      have ne : owner (N.attach p)≠owner v := fun eq => diff (owner.injective eq)
      simpa only [ite_eq_right ne] using got
  have rows := selected_slot_image count N v (pick y (owner v)) emit each
  simpa only [emit,copyIntervals,List.map_flatMap,List.filter_flatMap] using rows

variable {γ τ : Type*} [Fintype γ] [Fintype τ] {s C C' d d' k k' : ℕ}
    (F : Fields s old (groups*V) C d k w σ)
    (B : Fields s (old+4*(R+1)*V) ((R+1)*V) C' d' k' w τ)
    (oldPin : σ → γ) (newPin : τ → γ) (hd : d ≤ w) (zero : γ) (word : γ → Bool)
    (oldName : N.Site ↪ Fin s) (newName : N.Site ↪ Fin s)

/-- The actual combined Boolean frame returns the mathematical positive port
roster at every original site, including ports with coincident endpoints. -/
theorem physicalTile_siteRuns (hz : word zero=false)
    (rowMajor : ∀ p, oldPort p=finProdFinEquiv p)
    (before : Views.EndpointData N F oldName oldEdge oldPort (word ∘ oldPin))
    (after : Views.EndpointData out B newName edge port (word ∘ newPin))
    (oldRoom : ∀ v, incoming N v < 2^w) (newRoom : ∀ v, incoming out v < 2^w) (v : N.Site) :
    (Fragment.siteRuns (F.sites (oldName v)).val
      (Fragment.list ((physicalFrame F B oldPin newPin hd zero (slot count old hg small room)).eval word))).Perm
      ((Finset.univ.toList.flatMap (fun a : Attached N v =>
        (copyIntervals copies g (copiesAt v small a)).map (atOffset (portStart N oldEdge oldPort v a)))).filter
          (fun z => decide (0<z.width))) := by
  let name : N.Site ↪ ℕ := (oldName.trans F.sites).trans Fin.valEmbedding
  have col := TileColumns.of_physical G hV count N h hg small oldEdge oldPort F B oldPin newPin hd zero word
    oldName newName hz rowMajor before after oldRoom newRoom
  rw [physicalFrame_eval]
  exact tileFrame_siteRuns G hV count N h hg small oldEdge oldPort _ _ name col oldRoom newRoom v

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
