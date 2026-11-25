import OAI.Computability.BorderVNP.PackedRoutingExport

/-! # The real private assignment extent and original site staging addresses

The caller's remaining output array starts after the live placement pairs.
Its first words can provide the private assignment length per cell, followed
by the staging base of every original box and the internal-wire length per
cell. These references use the same physical address scan as cable offsets.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open CellAddressCircuit CellAddressViews CellAddressPhysical Crossing ParseBatchSort
open GeometryFrameEncoding VPVNP.VerifierNetwork

variable {s m n C d k w J A o : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

/-- Stable markers and sites to feed the owned-cell and original-box row producers. -/
noncomputable def privateViews (old : Fin J → Fin s) : Frame σ (Fin (C+(J+C)) × Fin w) :=
  (CellAddressViews.frame F).select fun q =>
    (Fin.addCases (fun c => .inr (.inr (1,c)))
      (Fin.addCases (fun i => .inr (.inl (old i))) (fun c => .inr (.inr (0,c)))) q.1,q.2)

/-- Appending these views leaves the geometry validity check and all subsequent words accessible. -/
noncomputable def withPrivateViews (old : Fin J → Fin s) (rest : Frame σ (Outputs o w)) :
    Frame σ (Outputs ((C+(J+C))+o) w) := GeometryOutput.prepend (privateViews F old) rest

/-- Only references to the address scan are selected. -/
theorem privateViews_size (old : Fin J → Fin s) : (privateViews F old).size = (CellAddressViews.frame F).size := rfl

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {x : σ → Bool} (net : Represents N cell aux siteID edgeID portID F x)
variable (fit : ∀ c, CellAddresses.guessedSize N cell c+CellAddresses.siteSize N cell c aux+
  CellAddresses.suppliedSize N cell c < 2^w)

include net fit

/-- The first appended array is the full private region length of each true cell,
used by the compact cell-call initializer. -/
theorem privateViews_wires (old : Fin J → Fin s) (c : Fin C) :
    value (fun j => (privateViews F old).eval x (c.castAdd (J+C),j)) =
      CellAddresses.guessedSize N cell c+CellAddresses.siteSize N cell c aux := by
  simpa [privateViews] using marker_value N cell aux siteID edgeID portID F net fit c 1

/-- The second array is the absolute staging base of each retained original box. -/
theorem privateViews_site (old : Fin J → N.Site) (i : Fin J) :
    value (fun j => (privateViews F (siteID ∘ old)).eval x (Fin.natAdd C (i.castAdd C),j)) =
      CellAddresses.siteBase N cell (cell (old i)) siteID aux ⟨old i,rfl⟩ := by
  simpa [privateViews] using site_value N cell aux siteID edgeID portID F net fit (old i)

/-- The final marker array is the start of site staging after the internal cable guesses. -/
theorem privateViews_internal (old : Fin J → Fin s) (c : Fin C) :
    value (fun j => (privateViews F old).eval x (Fin.natAdd C (Fin.natAdd J c),j)) =
      CellAddresses.guessedSize N cell c := by
  simpa [privateViews] using marker_value N cell aux siteID edgeID portID F net fit c 0

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
