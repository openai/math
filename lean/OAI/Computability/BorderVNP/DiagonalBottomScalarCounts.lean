import OAI.Computability.BorderVNP.DiagonalSewnTape
import OAI.Computability.BorderVNP.PackedGridWitnessIDs

/-! # No replacement scalar occurrences in the actual private bottom checker -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.Tracked

open Crossing Packing
open scoped Classical

variable {D exp : ℕ} {P Team Param Gadget : Type} [Fintype Team] [Fintype Param]
    {bits : P → ℕ} {N M : Network D P bits}

/-- Empty scalar multiplicities are preserved when the tagged tables are
installed through equality of their physical layouts. -/
theorem cast_no_gadgets (t : Tracked Team Param Gadget exp N) (eqn : N = M)
    (empty : ∀ v a x, (counters (t.tags v a x)).2 = 0) :
    ∀ v a x, (counters ((t.castLayout eqn).tags v a x)).2 = 0 := by
  cases eqn
  exact empty

variable {H A : Type} {N : Network D P (fun _ => 1)} (width : A → ℕ)
    (lane : P ↪ Σ a, Fin (width a)) (owner : A → N.Site)
    (aligned : ∀ p, owner (lane p).1 = N.attach p)
    (base : H → Tracked Team Param Gadget exp N)

/-- Concatenating copies and grouping the external tile words introduces
only existing factors and keeps every scalar multiplicity at zero. -/
theorem grouped_no_gadgets {copies : ℕ} (z : Fin copies → H)
    (empty : ∀ j v a x, (counters ((base j).tags v a x)).2 = 0)
    (v a x) : (counters ((groupedCopies width lane owner aligned base z).tags v a x)).2 = 0 :=
  repeat_no_gadgets (fun i => (base (z i)).tags) (fun i => empty (z i)) v a _

end Diagonal.CellEntries.Tracked

namespace Packing.DeckGrid.WiredWitness

open Crossing Diagonal.CellEntries Cover TeamContraction ParseBatch.Prewire
open Diagonal.ExternalSew.GridHosts
open scoped Classical

variable {D q depth R r t pins link inner n g copies : ℕ} {Edge Gadget : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {state : Fin g}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- The named grouped, routed seed checker contains precisely zero gadget
ID occurrences on every private assignment and every incident wire word. -/
theorem bundle_no_gadgets (z : Fin copies → W.Hidden position) (v a x) :
    (counters ((W.bundle (Gadget := Gadget) position copies z).tags v a x)).2 = 0 := by
  apply Tracked.grouped_no_gadgets
  intro j
  exact Tracked.cast_no_gadgets ⟨W.seedTags (Gadget := Gadget) position j,W.seedWords position j⟩
    (W.seedGrid_eq position) (W.seed_no_gadgets position j)

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
