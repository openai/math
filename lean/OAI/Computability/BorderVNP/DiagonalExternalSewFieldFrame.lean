import OAI.Computability.BorderVNP.DiagonalExternalSewFieldImage
import OAI.Computability.BorderVNP.DiagonalExternalFineView
import OAI.Computability.VPVNP.VerifierMachineSplice

/-! # Composition of the public sewn fields with the retained-history Boolean frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.FieldExport

open Crossing Packing.CellAddressCircuit Packing.CellAddressPhysical VPVNP.VerifierNetwork

/-- Exposing fine lanes for the contraction retains every *internal* sparse field.
No fine-lane directory is created or read. -/
theorem CoreColumns.fine {D s old n C d k w : ℕ} {A P : Type} {width : A → ℕ}
    {L : Network D A width} (lane : P ↪ Σ a, Fin (width a)) {cell : L.Site → Fin C} {aux : L.Site → ℕ}
    {siteID : L.Site ↪ Fin s} {edgeID : L.Edge ↪ Fin old} {σ : Type*} {F : Fields s old n C d k w σ}
    {x : σ → Bool} (h : CoreColumns L cell aux siteID edgeID F x) :
    CoreColumns (FineView.layout L lane) cell aux siteID edgeID F x :=
  ⟨h.owner,h.src,h.dst,h.edge,h.stage,h.edgeHole,h.stageHole⟩

/-- Add the sewn-field pins to a true public history frame. The dynamic internal
data is shared, and only two additional constant Boolean gates are needed. -/
noncomputable def withSewnFields {σ γ : Type*} [Fintype σ] [Fintype γ]
    (source : Frame γ σ) : Frame γ (σ ⊕ Bool) := (constants σ).subst source

/-- The composed gate count charges the entire prior public history. -/
theorem withSewnFields_size {σ γ : Type*} [Fintype σ] [Fintype γ] (source : Frame γ σ) :
    (withSewnFields source).size ≤ source.size+2 := by
  rw [withSewnFields,Frame.subst_size]
  exact Nat.add_le_add_left (constants_size _) _

/-- From the original compressed pack's already checked sparse field representation,
the composite public Boolean frame represents the actual physically sewn and
grouped network, with the exact same internal gate sharing and physical slot order. -/
theorem frame_represents {D s old n C d k w : ℕ} (p : Params) (hp : p.Valid)
    {A P : Type} {bits : A → ℕ} (L : Network D A bits) (lane : P ↪ Σ a, Fin (bits a))
    {phys : PublicPort p.R p.processors p.literal p.link ≃ P}
    (h : BlockHosts (FineView.layout L lane) phys p.g) (cell : L.Site → Fin C) (aux : L.Site → ℕ)
    (siteID : L.Site ↪ Fin s) (edgeID : L.Edge ↪ Fin old) (portID : A ↪ Fin n)
    {σ γ : Type*} [Fintype σ] [Fintype γ] (F : Fields s old n C d k w σ) (source : Frame γ σ) (y : γ → Bool)
    (checked : Represents L cell aux siteID edgeID portID F (source.eval y)) (name : ℕ → ℕ → ℕ)
    (host : ∀ (u : Fin (p.R+1)) i, i < p.sites → name u.val i = (F.sites (siteID (h.host (u,i)))).val)
    (word : p.g < 2^w) :
    Represents (finalLayout p h) cell aux siteID (mergedEdges p hp edgeID)
      finProdFinEquiv.toEmbedding (fields F p name) ((withSewnFields source).eval y) := by
  have vals : (withSewnFields source).eval y = (constants σ).eval (source.eval y) :=
    funext fun i => Frame.subst_eval _ _ y i
  rw [vals]
  exact sewn_represents p hp h cell aux siteID edgeID F _ ((CoreColumns.of_represents checked).fine lane)
    name host word

end Diagonal.ExternalSew.FieldExport

end BorderVNP
end Computability
end OAI
