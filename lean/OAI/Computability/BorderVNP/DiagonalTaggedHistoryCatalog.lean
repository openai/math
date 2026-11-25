import OAI.Computability.BorderVNP.DiagonalTaggedHistoryDense
import OAI.Computability.BorderVNP.ShortenCatalogProgram

/-! # Preserving a prepared catalog on the physical dense layout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Catalog

open Cover Epoch

variable {D d r : ℕ} {P I : Type} [Fintype I] {bits : P → ℕ} {K : Type*}
    {S : Finset (HyperbolicHost I)} {h : ℝ} {p : PlacedPack D P bits K I d}

/-- Saving the live cable rows preserves catalog membership, the short
segment bound, and the chosen midpoint inequality at every active cable. -/
theorem PlacedAt.dense (hs : PlacedAt S h p) (number : p.pack.layout.Edge ↪ Fin r) :
    PlacedAt S h (p.dense number) where
  sites := hs.sites
  short c hc := by
    obtain ⟨a,rfl⟩ := (Packing.Names.denseSlot p.pack.layout number).surjective c
    rw [(p.dense_marks number a).1] at hc
    rw [(p.dense_endpoints number a).1, (p.dense_endpoints number a).2]
    exact hs.short a hc
  midpoint c hc := by
    obtain ⟨a,rfl⟩ := (Packing.Names.denseSlot p.pack.layout number).surjective c
    have ha := ((p.dense number).active_iff _).mp hc
    rw [(p.dense_marks number a).1, (p.dense_endpoints number a).1, (p.dense_endpoints number a).2] at ha
    rw [(p.dense_marks number a).2, (p.dense_endpoints number a).1, (p.dense_endpoints number a).2]
    exact hs.midpoint a ((p.active_iff a).mpr ha)

end Shortening.Catalog

end BorderVNP
end Computability
end OAI
