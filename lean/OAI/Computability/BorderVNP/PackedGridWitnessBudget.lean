import OAI.Computability.BorderVNP.PackedGridFineCapacity
import OAI.Computability.BorderVNP.ParseBatchWiredWitness

/-! # Public capacities for the fixed private verifier in every actual seed-grid cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Crossing Diagonal.CellEntries GridPlacement Cover TeamContraction
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical

/-- Uniform capacity for old and inserted fine sites, in terms of the public
deck and batch parameters alone. -/
noncomputable def seedSiteCapacity (n r q depth : ℕ) :=
  siteCapacity (Fintype.card (Fin q → Deck (depth+2))) (r*n) (batchVolume n r) (q*(1+3*depth^3))

namespace WiredWitness

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- Use the same equality instance as the actual conditioned deck-grid table. -/
noncomputable local instance witnessBudgetDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _

/-- All old verifier vertices and all equality hops stored in the named cell fit
in the published one-copy factor capacity. -/
theorem seed_sites_le (c : Fin q → Deck (depth+2)) :
    Fintype.card {v : ((wiredFine G d D W.trees).subdivide (wireRoutes position W.route)).Site //
      cell position W.route v = c} ≤ seedSiteCapacity n r q depth :=
  routed_capacity (wiredFine G d D W.trees) finProdFinEquiv (wiredLayout G d W.trees).distinct_input_leaves
    order (r*n) _ position W.route ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans W.volume)) c

/-- The actual guessed and supplied per-copy bit lanes of the sparse box fit in
three times the same public capacity, independent of private route choices. -/
theorem seed_stride_le (c : Fin q → Deck (depth+2)) :
    GridBoxes.stride ((wiredFine G d D W.trees).subdivide (wireRoutes position W.route)) (cell position W.route) c ≤
      3*seedSiteCapacity n r q depth :=
  routed_stride (wiredFine G d D W.trees) finProdFinEquiv (wiredLayout G d W.trees).distinct_input_leaves
    order (r*n) _ position W.route (BooleanLayout.trivalent (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d))
    ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans W.volume)) c

include position in
/-- Distinct live weighted positions in a cell occupy distinct true verifier
vertices even if all their public owner names coincide. -/
theorem seed_report_count (c : Fin q → Deck (depth+2)) :
    Fintype.card {j : WeightSites n g r d // finePlace G d D q depth order W.trees
      (BooleanLayout.weightSite (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) j) = c} ≤
      seedSiteCapacity n r q depth := by
  let sites := BooleanLayout.weightSite (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d)
  let f : {j // finePlace G d D q depth order W.trees (sites j) = c} →
      {v : ((wiredFine G d D W.trees).subdivide (wireRoutes position W.route)).Site // cell position W.route v = c} :=
    fun j => ⟨.inl (sites j.val),j.property⟩
  apply (Fintype.card_le_of_injective f ?_).trans (W.seed_sites_le position c)
  intro a b hab
  apply Subtype.ext
  exact sites.injective (Sum.inl.inj (congrArg Subtype.val hab))

end WiredWitness
end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
