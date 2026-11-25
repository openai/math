import OAI.Computability.BorderVNP.CubeRouteCommonDemands
import OAI.Computability.BorderVNP.PackedRoutingPlaced

/-! # One ordered compacted demand list from the actual private and live geometry on every team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA
open scoped Classical

/-- Genuine geometry images of the same packed network yield one common list of data demands.
The selected memories and the locations of their placement tables may vary by team. Only
positive-width records contribute to the physical list. -/
theorem packed_exterior_directory {K s m n C d k b W : ℕ} {T : Type*} (ref : T) {P : Type*} [Fintype P] {bits : P → ℕ}
    {σ : Type*} [Fintype σ] (D : Directory.Layout) (N : Network K P bits) (cell : N.Site → Fin C)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : T → Fields s m n C d k b σ) (x : T → σ → Bool)
    (net : ∀ u, Represents N cell aux siteID edgeID portID (F u) (x u))
    (ids : ∀ u c, ((F u).cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (original : Fin D.entries → N.Site) (live : (Fin D.teams × Fin D.sites) ↪ P)
    (width : ∀ t, bits (live t)=D.block) (bounds : D.DestinationBounds)
    (head origin : T → ℕ) (gap : ℕ) (before after : T → ℕ → ℕ)
    (geometry : ∀ u, Image (F u) (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) (x u) (origin u) (before u))
    (placed : ∀ u, (privateLayout (head u) (origin u) m C D.entries D.description gap).Image (before u) D.entries (after u))
    (room : ∀ u, (privateLayout (head u) (origin u) m C D.entries D.description gap).Fits W (before u)) :
    let pp := fun u => Directory.ISA.placement (after u) (bases (origin u) m C D.entries).privatePairs
    let lp := fun u => Directory.ISA.placement (after u) (bases (origin u) m C D.entries).livePairs
    ∀ u, D.directory (pp u) (lp u) = D.directory (pp ref) (lp ref) := by
  intro pp lp u
  let place (t : T) := (geometry t).networkPlacement N cell aux siteID edgeID portID
    (F t) (net t) (ids t) fit D original live width (head t) (origin t) gap (before t) (after t) (placed t) (room t)
  exact (place u).directory_eq (place ref) (fun _ => rfl) bounds

/-- Reading the canonical directory from team zero. -/
theorem packed_common_directory {R K s m n C d k b W : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    {σ : Type*} [Fintype σ] (D : Directory.Layout) (N : Network K P bits) (cell : N.Site → Fin C)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : Fin (R+1) → Fields s m n C d k b σ) (x : Fin (R+1) → σ → Bool)
    (net : ∀ u, Represents N cell aux siteID edgeID portID (F u) (x u))
    (ids : ∀ u c, ((F u).cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (original : Fin D.entries → N.Site) (live : (Fin D.teams × Fin D.sites) ↪ P)
    (width : ∀ t, bits (live t)=D.block) (bounds : D.DestinationBounds)
    (head origin : Fin (R+1) → ℕ) (gap : ℕ) (before after : Fin (R+1) → ℕ → ℕ)
    (geometry : ∀ u, Image (F u) (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) (x u) (origin u) (before u))
    (placed : ∀ u, (privateLayout (head u) (origin u) m C D.entries D.description gap).Image (before u) D.entries (after u))
    (room : ∀ u, (privateLayout (head u) (origin u) m C D.entries D.description gap).Fits W (before u)) :
    let pp := fun u => Directory.ISA.placement (after u) (bases (origin u) m C D.entries).privatePairs
    let lp := fun u => Directory.ISA.placement (after u) (bases (origin u) m C D.entries).livePairs
    ∀ u, D.directory (pp u) (lp u) = D.directory (pp 0) (lp 0) :=
  packed_exterior_directory 0 D N cell aux siteID edgeID portID F x net ids fit original live width bounds
    head origin gap before after geometry placed room

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
