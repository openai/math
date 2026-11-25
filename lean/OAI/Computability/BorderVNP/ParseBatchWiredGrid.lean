import OAI.Computability.BorderVNP.ParseBooleanGrid
import OAI.Computability.BorderVNP.ParseBatchPrewireValue

/-! # Within-team links are private before placement on the public deck grid -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Crossing Diagonal.CellEntries GridPlacement Cover TeamContraction
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar MvPolynomial
open scoped BigOperators Classical

variable {R r t pins link inner n : ℕ} {Edge : Type} [Fintype Edge]
    (G : Wiring R r t pins link inner n Edge)

omit [Fintype Edge] in
private theorem free_slots_le : r * publicWidth G ≤ r*n :=
  Nat.mul_le_mul_left r ((Nat.le_add_right (publicWidth G) inner).trans G.fits)

/-- Uniform public layout for the actual live fields. There are no public
ports for interior handoffs, sorter messages, zero clamps or trailing padding.
The address block width uses the entire r*n-slot envelope of Section 7.3. -/
noncomputable def wiredGrid {D : ℕ} (q depth : ℕ)
    (order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2)))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) :
    Network D (Fin r × Fin (publicWidth G)) (fun _ => 1) :=
  publicGridSlots position (step q (depth+2)) finProdFinEquiv order (fun _ => 1) (r*n) (free_slots_le G)
    (batchVolume n r) (q*(1+3*depth^3))

/-- The precise repeated bottom-grid realization, after every within-team
physical variable has become a private verifier input. Only the public
literal/exterior/pin field ordinals are handed to the placement procedure.
The same term family works over every coefficient ring and all field values. -/
theorem tagged_wired_batch_bundle {Gadget : Type} {D g s : ℕ} (q depth copies : ℕ)
    (d : Fin n) (state : Fin g) (hn : n = d.val+1) (hg : g ≤ 2*n+s+1) (hr : (n+s+2)^24 ≤ r)
    (hedge : Fintype.card Edge ≤ r*inner)
    (order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2)))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) :
    let M := (wiredGrid G q depth order position).repeatGrid copies
    let Param := GrammarLabel (Fin n × Bool) (Fin g) n
    ∃ (Hidden : Type) (_ : Fintype Hidden) (term : Hidden → M.Tables (Diagonal.CellEntries.Entry Param Gadget)),
      (∀ z, Nonempty (PowerWords (Fin copies × Unit) Param Gadget
        (Nat.clog 2 (r*(2*d.val+1)+1)) M (term z))) ∧
      ∀ (E : Type*) [CommRing E] (values : Gadget → E)
        (x : Fin copies → (Fin r × Fin (publicWidth G)) → Bool),
        (∑ z, M.value (fun v a y => interpret values (term z v a y)) (fun p _ => x p.1 p.2)) =
        ∏ i, MvPolynomial.map (Int.castRingHom E) (∑ int : Edge → Bool,
          ∏ j, labelQuery d state (fun l => readInput (Function.uncurry (source G)) (x i) int (j,l))) := by
  obtain ⟨trees,ht,hv,_⟩ := batched_queries d state hn hg hr
  let c := verifier d trees
  let f := Function.uncurry (source G)
  let c' := Prewire.circuit (projection f) c
  let weight := weightedPin (m := n) (g := g) (r := r) (d := d)
  let w' : WeightSites n g r d → Edge ⊕ _ := fun j => Sum.inr (weight j)
  have hV := (rewire_volume f c weight (card_public_private_le G hedge)).trans hv
  obtain ⟨H,inst,term,words,eqv⟩ := tagged_verifier_bundle (Gadget := Gadget) c' w'
    (batchVolume n r) (q*(1+3*depth^3)) copies hV position (step q (depth+2))
    (inverse_letter q (depth+2)) (short_words q depth) finProdFinEquiv order (r*n) (free_slots_le G)
  refine ⟨H,inst,term,words,?_⟩
  intro E _ values x
  refine (eqv E values x).trans ?_
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (MvPolynomial.map (Int.castRingHom E))
  refine (rewire_value f c weight BooleanLayout.powerWeight (x i)).trans ?_
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro z _
  exact ht (fun j l => readInput f (x i) z (j,l))

/-- On the actual physical field values the rewired batch factor is the
substituted query product with each interior edge summed exactly once. -/
theorem wired_queries_actual {g : ℕ} (d : Fin n) (state : Fin g)
    (team : Fin (R+1)) (pin : Fin pins → Bool) (ext : Exterior R r link → Bool) :
    (∑ int : Edge → Bool, ∏ j, labelQuery d state (fun l =>
      readInput (Function.uncurry (source G)) (publicBits G team pin ext) int (j,l))) =
      ∑ int : Edge → Bool, ∏ j, labelQuery d state (G.word pin ext int team j) := by
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.prod_congr rfl
  intro j _
  exact congrArg (labelQuery d state) (funext (source_read G team pin ext z j))

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
