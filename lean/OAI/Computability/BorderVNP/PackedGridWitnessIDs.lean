import OAI.Computability.BorderVNP.PackedGridWitnessUse

/-! # Original seed verifier terms carry no replacement gadget identifiers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Packing ParseBatch VPVNP.BooleanTranscript
open scoped BigOperators Classical
variable {Param Gadget : Type}

/-- A finite product of entries with empty gadget vectors still has an empty
gadget vector, also when the product rejects. -/
theorem product_no_gadgets {I : Type} [Fintype I] (f : I → Entry Param Gadget)
    (h : ∀ i, (counters (f i)).2 = 0) : (counters (∏ i, f i)).2 = 0 := by
  by_cases hp : ∏ i, f i = 0
  · rw [hp]; rfl
  · rw [counters_prod f (fun i => Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ _)),counters_passed]
    simp [h]

/-- Every old site of the Boolean verifier is an ordinary check or a parameter
unary. Both have zero replacement gadget count. -/
theorem powerTags_no_gadgets {X W : Type} [Fintype X] [Fintype W] [Fintype Param] {s b : ℕ}
    (c : Circuit (X ⊕ W) s) (weighted : Param × Fin b → W) (v a x) :
    (counters (BooleanLayout.powerTags (Gadget := Gadget) c weighted v a x)).2 = 0 := by
  unfold BooleanLayout.powerTags
  split
  · unfold unary
    dsimp only
    split <;> rfl
  · split <;> rfl

variable {D : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}
    {tags : N.Tables (Entry Param Gadget)}

/-- Subdivision preserves empty gadget counts at every original site and creates
only ordinary equality checks at the inserted vertices. -/
theorem subdivide_no_gadgets (routes : N.WireRoutes) (h : ∀ v a x, (counters (tags v a x)).2 = 0)
    (v a x) : (counters (N.subdivideTables routes tags v a x)).2 = 0 := by
  rcases v with old | eq
  · exact h old _ _
  · dsimp only [Network.subdivideTables]
    split <;> rfl

variable {Cell Q : Type} [Fintype Cell] [DecidableEq Cell] [Fintype Q]
    (cell : N.Site → Cell) (position : Cell → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (hidden : ∀ i, N.InsideAssignment cell i) {src dst : Q → Cell} {H : ℕ}
    (packing : (N.cellNetwork cell position).ChannelPacking src dst H)

/-- Hidden-word conditioning, site multiplication, unpacking and zero padding
preserve the empty gadget vector for every seed cell entry. -/
theorem conditioned_no_gadgets (h : ∀ v a x, (counters (tags v a x)).2 = 0) (v a x) :
    (counters (conditionedGridTags cell position packing tags hidden v a x)).2 = 0 := by
  unfold conditionedGridTags paddedFactor
  split
  · apply product_no_gadgets
    intro fine
    exact h fine.val _ _
  · rfl

/-- Each copy of the initial checker has the same empty gadget-ID list.
Concatenating the physical lanes of the bottom bundle preserves that fact. -/
theorem repeat_no_gadgets {copies : ℕ} (terms : Fin copies → N.Tables (Entry Param Gadget))
    (h : ∀ i v a x, (counters (terms i v a x)).2 = 0) (v a x) :
    (counters (repeatedTags terms v a x)).2 = 0 :=
  product_no_gadgets _ (fun i => h i v _ _)

end Diagonal.CellEntries

namespace Packing.DeckGrid.WiredWitness

open Crossing Diagonal.CellEntries GridPlacement Cover TeamContraction
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {Gadget : Type}

/-- Use the same equality instance as the actual conditioned deck-grid table. -/
noncomputable local instance witnessIDsDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _

/-- Concrete base case of gadget accounting for the actual fixed seed grid. -/
theorem seed_no_gadgets (z : W.Hidden position) (v a x) :
    (counters (W.seedTags (Gadget := Gadget) position z v a x)).2 = 0 :=
  conditioned_no_gadgets (cell position W.route) position z (routedPacking position W.route (fun _ => le_rfl))
    (subdivide_no_gadgets (wireRoutes position W.route)
      (powerTags_no_gadgets (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d))) v a x

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
