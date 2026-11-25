import OAI.Computability.BorderVNP.PackedBundleGeometryHeaders
import OAI.Computability.BorderVNP.PackedBottomWiredSite
import OAI.Computability.BorderVNP.PackedSeedCoreChoices

/-! # Six scalar sort fields for an original verifier slab -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing Cover Packing BottomReports Inherited CellSparse Diagonal.ExternalSew
open ParseBatch ParseBatchVerifier Prewire TeamContraction VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- Static copy count, padded fine width, incoming width and reserved report
lanes used by the source site's concrete six-word header emitter. -/
noncomputable def seedBundleShape (c : Fin q → Deck (depth+2)) (copies : ℕ) : BundleSort.Shape :=
  ⟨copies,3*seedSiteCapacity n r q depth,incoming (W.seedGrouped position) c,seedSiteCapacity n r q depth⟩

/-- The source shape produces the same six words as the actual typed report. -/
theorem seedBundleShape_header (c : Fin q → Deck (depth+2)) (slots base copies : ℕ) :
    (W.seedBundleShape position c copies).header slots base = W.seedUseHeader position c slots base copies := rfl

/-- The physical sort's dimensions come from exactly the same one-copy
private slab whose individual fine and reported bits the runtime interprets. -/
theorem seedBundleShape_slab (c : Fin q → Deck (depth+2)) (copies : ℕ)
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {s m p : ℕ}
    (sid : (W.routedFine position).Site ↪ Fin s) (eid : (W.routedFine position).Edge ↪ Fin m)
    (pid : Fin r × Fin (publicWidth G) ↪ Fin p) :
    let layout := W.seedBundleShape position c copies
    let slab := W.seedSlab position code sid eid pid c
    layout.copies=copies ∧ layout.fine=slab.capFine ∧ layout.incoming=slab.incoming ∧
      layout.cap=slab.capReport ∧ bottomStride (layout.fine+layout.incoming) layout.cap=slab.stride := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Actual total header stride for a single copy fits the padded source-site
capacity including the private box and copied cable spans. -/
theorem seedBundleShape_stride (c : Fin q → Deck (depth+2)) (copies : ℕ) :
    let sh := W.seedBundleShape position c copies
    bottomStride (sh.fine+sh.incoming) sh.cap ≤ seedBoxCapacity n r q depth (Fintype.card (Direction q)) :=
  (Nat.le_add_left _ _).trans (W.seedBorn_room position c)

/-- Row-major source of one bundle per original tile in every public leaf. -/
noncomputable def frozenBundleShapes (leaves copies : ℕ)
    (j : Fin (leaves*GridHosts.tileCount q depth)) : BundleSort.Shape :=
  W.seedBundleShape position (order (finProdFinEquiv.symm j).2) copies

/-- The scanner's original report header, including its offset and absolute
description pointer, is produced at the original row-major address. -/
theorem frozenBundleShapes_header (leaves copies : ℕ) (j : Fin (leaves*GridHosts.tileCount q depth)) (slot base : ℕ) :
    (W.frozenBundleShapes position leaves copies j).header slot base =
      W.seedUseHeader position (order (finProdFinEquiv.symm j).2) slot base copies := rfl

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
