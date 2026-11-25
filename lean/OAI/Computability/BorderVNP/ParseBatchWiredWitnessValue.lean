import OAI.Computability.BorderVNP.ParseBatchWiredWitness

/-! # Contractions of the actual routed witness before the literal installation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing Diagonal.CellEntries GridPlacement Cover TeamContraction
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar MvPolynomial
open scoped BigOperators Classical

variable {D q depth R r t pins link inner n g : ℕ} {Edge Gadget : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {state : Fin g}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {E : Type*} [CommRing E] (values : Gadget → E)

/-- Sum the actual privately conditioned routed terms, in the public graph of
this specific named witness. Only the team's physical interior variables are
summed in the resulting query polynomial. -/
theorem seed_value (y : (Fin r × Fin (publicWidth G)) → Bool) :
    (∑ z : W.Hidden position, (W.seedGrid position).value
      (fun v a x => interpret values (W.seedTags position z v a x)) (fun p _ => y p)) =
    MvPolynomial.map (Int.castRingHom E) (∑ int : Edge → Bool,
      ∏ j, labelQuery d state (fun l => readInput (Function.uncurry (source G)) y int (j,l))) := by
  have hv := sum_privateGrid_value (tags := W.fineTags) position W.route
    (fun _ => le_rfl) values (fun p _ => y p)
  refine (Finset.sum_congr (Finset.ext fun _ => by simp) fun _ _ => rfl).trans (hv.trans ?_)
  refine (BooleanLayout.powerTags_value (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) values y).trans ?_
  apply congrArg (MvPolynomial.map (Int.castRingHom E))
  let f := Function.uncurry (source G)
  refine (rewire_value f (verifier d W.trees) weightedPin BooleanLayout.powerWeight y).trans ?_
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro h _
  exact W.computes (fun j l => readInput f y h (j,l))

/-- The exact named witness, after plugging in the real per-team fields. -/
theorem seed_value_actual (team : Fin (R+1)) (pin : Fin pins → Bool) (ext : Exterior R r link → Bool) :
    (∑ z : W.Hidden position, (W.seedGrid position).value
      (fun v a x => interpret values (W.seedTags position z v a x)) (fun p _ => publicBits G team pin ext p)) =
    MvPolynomial.map (Int.castRingHom E) (∑ int : Edge → Bool, ∏ j, labelQuery d state (G.word pin ext int team j)) :=
  (W.seed_value position values _).trans (congrArg (MvPolynomial.map (Int.castRingHom E))
    (wired_queries_actual G d state team pin ext))

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
