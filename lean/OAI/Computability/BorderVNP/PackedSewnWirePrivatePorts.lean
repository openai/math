import OAI.Computability.BorderVNP.PackedSewnWireImage
import OAI.Computability.BorderVNP.FiniteCandidatePortNames

/-! # Identifying the flattened private port rows in the retained-wire intervals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Crossing Inherited Diagonal.ExternalSew

variable {D : ℕ} {A P U Free Cable : Type} [Fintype A] [Fintype U] [Fintype Cable]
    {bits : A → ℕ} (L : Network D A bits) (lane : P ↪ Σ a, Fin (bits a))
    {cw : Cable → ℕ} (B : Bundle (FineView.layout L lane) Free Cable cw)
    (gw : U → ℕ) (owner : U → L.Site)
    {ae ap aq be bp : ℕ} (oldEdge : L.Edge ↪ Fin ae) (before : A ↪ Fin ap) (other : A ↪ Fin aq)
    (edge : (L.Edge ⊕ Cable) ↪ Fin be) (port : U ↪ Fin bp)

/-- Relabelling the port capacity by equality and preserving each actual row number
preserves the full old-to-new cable interval. -/
theorem wireInterval_ports (capacity : ap=aq) (same : ∀ z, (before z).val=(other z).val)
    (v : L.Site) (z : Incident L v) :
    wireInterval L lane B gw owner oldEdge before edge port v z =
      wireInterval L lane B gw owner oldEdge other edge port v z := by
  subst aq
  obtain rfl : before=other := DFunLike.ext _ _ fun z => Fin.ext (same z)
  rfl

end Packing.SewnField

end BorderVNP
end Computability
end OAI
