import OAI.Computability.BorderVNP.PackedSewnWireRoute

/-! # Physical input shared by the two terminal interval directories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open Crossing Inherited CellAddressCircuit Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport

/-- Cable and port pointers on both sides of exterior sewing, evaluated on one actual
Boolean assignment. The incidence counts bound every singleton prefix sum. -/
structure FieldReads {D s m n C d k w : ℕ} {A P σ : Type} [Fintype A] {bits : A → ℕ}
    (L : Network D A bits) (p : Params) (hp : p.Valid) (lane : P ↪ Σ a, Fin (bits a))
    {physical : PublicPort p.R p.processors p.literal p.link ≃ P} (hosts : BlockHosts (FineView.layout L lane) physical p.g)
    (siteID : L.Site ↪ Fin s) (edgeID : L.Edge ↪ Fin m) (portID : A ↪ Fin n)
    (F : Fields s m n C d k w σ) (name : ℕ → ℕ → ℕ) (present : Fin m → σ) (word : σ ⊕ Bool → Bool)
    (extent : L.Site → ℕ) : Prop where
  /-- The constant false input of the combined source. -/
  zero : word (.inr false) = false
  /-- Genuine physical pointers and widths before sewing. -/
  before : Views.EndpointData L F siteID edgeID portID (word ∘ Sum.inl)
  /-- Genuine physical pointers and widths after sewing. -/
  after : Views.EndpointData (finalLayout p hosts) (FieldExport.fields F p name) siteID (mergedEdges p hp edgeID)
    finProdFinEquiv.toEmbedding word
  /-- All original incidence ranges fit in the selected word width. -/
  oldRoom : ∀ v, incoming L v < 2^w
  /-- All final incidence ranges fit in the selected word width. -/
  newRoom : ∀ v, incoming (finalLayout p hosts) v < 2^w
  /-- The whole old private site extent occupies the retained prefix of its new staging bank. -/
  retained : ∀ v, ParseBatchSort.value ((word ∘ Sum.inl) ∘ F.auxWidth (siteID v)) = extent v
  /-- The full post-sewing extent fits the same word width. -/
  stagedRoom : ∀ v, extent v + incoming (finalLayout p hosts) v < 2^w
  /-- A retained physical cable occupies exactly its original stable row. -/
  occupied : ∀ i, word (.inl (present i)) = true ↔ i ∈ Set.range edgeID

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
