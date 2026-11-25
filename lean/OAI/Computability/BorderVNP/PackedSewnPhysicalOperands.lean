import OAI.Computability.BorderVNP.PackedSewnGridSourceImage
import OAI.Computability.BorderVNP.PackedSewnTileImage
import OAI.Computability.BorderVNP.PackedSewnTileOwners
import OAI.Computability.BorderVNP.PackedSewnWireOwners

/-! # The full physical source frame of the exterior-sewn verifier -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Crossing Inherited Diagonal.ExternalSew

/-- Identical named old-port rows induce the same complete pulled-back source map after
changing the presentation of their finite capacity. -/
theorem sewnRead_ports {D : ℕ} {A P U Free Cable : Type} [Fintype A] [Fintype P] [Fintype U] [Fintype Cable]
    {bits : A → ℕ} (N : Network D A bits) (lane : P ↪ Σ a, Fin (bits a))
    {cw : Cable → ℕ} (B : Bundle (FineView.layout N lane) Free Cable cw)
    (gw : U → ℕ) (free : Free ↪ Σ u, Fin (gw u)) (owner : U → N.Site)
    (aligned : ∀ f, owner (free f).1 = B.layout.attach f)
    {ae ap aq be bp : ℕ} (oldEdge : N.Edge ↪ Fin ae) (before : A ↪ Fin ap) (other : A ↪ Fin aq)
    (edge : (N.Edge ⊕ Cable) ↪ Fin be) (port : U ↪ Fin bp) (capacity : ap=aq)
    (same : ∀ z, (before z).val=(other z).val) (v : N.Site) :
    sewnRead N lane B gw free owner aligned oldEdge before edge port v =
      sewnRead N lane B gw free owner aligned oldEdge other edge port v := by
  subst aq
  obtain rfl : before=other := DFunLike.ext _ _ fun z => Fin.ext (same z)
  rfl

end Packing.SewnField

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

variable {σ : Type} [Fintype σ] {s C k w : ℕ} (F : Fields s old (groups*V) C w k w σ)
    (name : ℕ → ℕ → ℕ) (present : Fin old → σ)
local notation "B" => FieldExport.fields F params name
local notation "tileRows" => Fragment.Tile.slot count old hg small room
local notation "cables" => WireFragments.sewnFrame F params name present
local notation "tiles" => Fragment.Tile.physicalFrame F B Sum.inl id le_rfl (Sum.inr false) tileRows

/-- The actual two-pass raw operand source on the common old and sewn field pins. Its
shape depends on the public geometry and copy counts, before any slot valuation. -/
noncomputable def physicalOperands : Frame (σ ⊕ Bool) (Fragment.Pin (2*old + 6*(R+1)*V) w) :=
  Fragment.joinFrame cables tiles

local notation "raw" => physicalOperands G hV count hg small F name present
variable (siteID : N.Site ↪ Fin s) (x : σ ⊕ Bool → Bool)
local notation "key" => fun v => (F.sites (siteID v)).val
local notation "read₀" => sewnRead N lane h.bundle (fun _ : FreeBlock R V => g) (freeLane hg room)
    h.groupOwner (h.groupAligned hg room) oldEdge oldPort edge port

/-- The literal joined operand frame covers the true sewn partial map at every old host.
Every original lane has exactly one row occurrence, and every emitted row has a real
host. Both source passes read the same actual old and post-sew directory fields. -/
theorem physicalOperands_image (zero : x (.inr false) = false)
    (rowMajor : ∀ p, oldPort p=finProdFinEquiv p)
    (before : Views.EndpointData N F siteID oldEdge oldPort (x ∘ Sum.inl))
    (after : Views.EndpointData out B siteID edge port x)
    (occupied : ∀ i, x (.inl (present i)) = true ↔ i ∈ Set.range oldEdge)
    (oldFit : ∀ v, incoming N v < 2^w) (newFit : ∀ v, incoming out v < 2^w) :
    let xs := Fragment.list ((raw).eval x)
    (∀ p ∈ xs, ∃ v, p.site=(key) v) ∧ ∀ v, Covers (Fragment.siteRuns ((key) v) xs) (read₀ v) ∧
      Fragment.UniqueCover (incoming N v) (Fragment.siteRuns ((key) v) xs) := by
  intro xs
  let valid : (params).Valid := ⟨hg,small,room⟩
  have fields := TileColumns.of_physical G hV count N h hg small oldEdge oldPort F B Sum.inl id le_rfl (.inr false)
    x siteID siteID zero rowMajor before after oldFit newFit
  constructor
  · apply Fragment.joinFrame_owners cables tiles x key
    · exact WireFragments.owners_of_sewn N siteID oldEdge F params name present valid lane h x after
    · rw [physicalFrame_eval F B Sum.inl id le_rfl (.inr false) tileRows x]
      exact tile_owners G hV count N h hg small oldEdge oldPort _ _ key fields oldFit newFit
  · intro v
    apply joined_source_image G hV count N h hg oldEdge oldPort edge port v small cables tiles x ((key) v)
    · have wires := WireFragments.sewn_siteRuns N siteID oldEdge oldPort F params name present valid lane h x before after
        oldFit newFit occupied v Finset.univ.toList Finset.univ.nodup_toList (by simp)
      rw [List.filter_map]
      exact wires
    · exact physicalTile_siteRuns G hV count N h hg small oldEdge oldPort F B Sum.inl id le_rfl (.inr false)
        x siteID siteID zero rowMajor before after oldFit newFit v

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
