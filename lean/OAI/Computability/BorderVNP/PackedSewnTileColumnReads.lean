import OAI.Computability.BorderVNP.PackedInheritedEndpointViews

/-! # Both physical endpoints of a sewn cable in the virtual singleton-site address scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Views

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical CellAddressViews ParseBatchSort VPVNP.VerifierNetwork
open private virtual_rep from OAI.Computability.BorderVNP.PackedInheritedEndpointViews
open private capacity from OAI.Computability.BorderVNP.PackedInheritedAddress

variable {D s m n C d k w : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)
variable (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n) {x : σ → Bool}
variable (h : EndpointData N F siteID edgeID portID x) (fit : ∀ v, incoming N v < 2^w)

include h fit in
/-- The source column of the endpoint-only frame gives the exact site-local wire start. -/
theorem source_from_endpoints (e : N.Edge) :
    value (fun j => (frame F).eval x (.inl (Layer.edgeEnd (edgeID e) true),j)) =
      wireStart N edgeID portID (N.src e) ⟨e,Or.inl rfl⟩ := by
  change value (fun j => (frame F).eval x (.inl (.inl (.inl (edgeID e))),j)) = _
  simp only [frame,Frame.subst_eval]
  exact (CellAddressViews.source_value N siteID (fun _ => 0) siteID edgeID portID (fields F)
    (virtual_rep N F siteID edgeID portID h) (capacity N siteID fit) e).trans (wire_relabel N siteID edgeID portID _ _)

include h fit in
/-- The destination column also reads the shared input on a self-loop. -/
theorem dest_from_endpoints (e : N.Edge) :
    value (fun j => (frame F).eval x (.inl (Layer.edgeEnd (edgeID e) false),j)) =
      wireStart N edgeID portID (N.dst e) ⟨e,Or.inr rfl⟩ := by
  change value (fun j => (frame F).eval x (.inl (.inl (.inr (edgeID e))),j)) = _
  simp only [frame,Frame.subst_eval]
  exact (CellAddressViews.dest_value N siteID (fun _ => 0) siteID edgeID portID (fields F)
    (virtual_rep N F siteID edgeID portID h) (capacity N siteID fit) e).trans (wire_relabel N siteID edgeID portID _ _)

end Packing.Inherited.Views

end BorderVNP
end Computability
end OAI
