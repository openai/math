import OAI.Computability.BorderVNP.ParseBatchWiredWitnessValue
import OAI.Computability.BorderVNP.DiagonalGroupedCopies
import OAI.Computability.BorderVNP.DiagonalExternalGridHosts

/-! # Named, physically grouped bottom bundles of the substituted row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing Diagonal.CellEntries Cover TeamContraction ParseBatch ParseBatchVerifier
open Prewire Diagonal.ExternalSew.GridHosts VPVNP VPVNP.ParseGrammar MvPolynomial
open scoped BigOperators Classical

variable {R r pins link n D q depth t inner g : ℕ} {Edge Gadget : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {state : Fin g}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- The true private assignments and local tables of the named fine
verifier installed in the public zero-literal directory. -/
noncomputable def seed (z : W.Hidden position) : Tracked Unit
    (GrammarLabel (Fin n × Bool) (Fin g) n) Gadget (Nat.clog 2 (r*(2*d.val+1)+1))
    (wiredGrid G q depth order position) :=
  Tracked.castLayout (W.seedGrid_eq position) ⟨W.seedTags position z,W.seedWords position z⟩

/-- The field-polynomial value of these transported public tables. -/
theorem seed_read {E : Type*} [CommRing E] (values : Gadget → E)
    (x : Fin r × Fin (publicWidth G) → Bool) :
    (∑ z : W.Hidden position, ((W.seed position z).valued values).tensor (fun p _ => x p)) =
      MvPolynomial.map (Int.castRingHom E) (∑ int : Edge → Bool,
        ∏ j, labelQuery d state (fun l => readInput (Function.uncurry (source G)) x int (j,l))) := by
  refine (Finset.sum_congr (Finset.ext fun _ => by simp) fun z _ => ?_).trans (W.seed_value position values x)
  exact Tracked.castLayout_tensor (W.seedGrid_eq position) ⟨W.seedTags position z,W.seedWords position z⟩ values _

/-- The actual table in a repeated, grouped public tile. The named original
seed, route and private choices are kept as data. -/
noncomputable def bundle (copies : ℕ) (z : Fin copies → W.Hidden position) :
    Tracked (Fin copies × Unit) (GrammarLabel (Fin n × Bool) (Fin g) n) Gadget
      (Nat.clog 2 (r*(2*d.val+1)+1))
      ((wiredGrid G q depth order position).groupedRepeat
        (fun _ : Fin (Fintype.card (Fin q → Deck (depth+2))) => blockWidth (r*n) (Fintype.card (Fin q → Deck (depth+2))))
        order copies) :=
  Tracked.groupedCopies _ (wiredLane G _ Fintype.card_pos) order (wired_aligned G q depth order position)
    (W.seed position) z

/-- The fields of all original processors, read back from the actual grouped
addresses. Private fine assignments vary independently across copies. -/
theorem bundle_read {E : Type*} [CommRing E] (values : Gadget → E) (copies : ℕ)
    (x : Ports (fun _ : Fin (Fintype.card (Fin q → Deck (depth+2))) =>
      copies*blockWidth (r*n) (Fintype.card (Fin q → Deck (depth+2)))))
    (fields : Fin copies → Fin r × Fin (publicWidth G) → Bool)
    (reads : ∀ i p, let a := Network.repeatLane (fun _ : Fin (Fintype.card (Fin q → Deck (depth+2))) =>
      blockWidth (r*n) (Fintype.card (Fin q → Deck (depth+2)))) (wiredLane G _ Fintype.card_pos) copies (i,p)
      x a.1 a.2 = fields i p) :
    (∑ z : Fin copies → W.Hidden position, ((W.bundle position copies z).valued values).tensor x) =
      ∏ i, MvPolynomial.map (Int.castRingHom E) (∑ int : Edge → Bool,
        ∏ j, labelQuery d state (fun l => readInput (Function.uncurry (source G)) (fields i) int (j,l))) := by
  refine (Tracked.sum_groupedCopies _ (wiredLane G _ Fintype.card_pos) order
    (wired_aligned G q depth order position) (W.seed position) values x).trans ?_
  apply Finset.prod_congr rfl
  intro i _
  refine Eq.trans ?_ (W.seed_read position values (fields i))
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg ((W.seed position z).valued values).tensor
  funext p _
  exact reads i p

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
