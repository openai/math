import OAI.Computability.BorderVNP.ParseBatchWiredSubstitution
import OAI.Computability.BorderVNP.PackedGridLanes

/-! # Named fine verifier and routes of the actual interior-wired bottom grid

The fixed tree checker, rewired gate table, sparse unary positions and ordered
Cayley paths are retained in the witness. The private assignment type and
the table read at a grid box are computed directly from these objects.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Crossing Diagonal.CellEntries GridPlacement Cover TeamContraction
open ParseBatch ParseBatchVerifier ParseBatchTrees Prewire VPVNP VPVNP.ParseGrammar VPVNP.VerifierNetwork
open scoped BigOperators Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    (G : Wiring R r t pins link inner n Edge) (d : Fin n)

/-- The exposed Boolean circuit with the team's actual interior references installed. -/
noncomputable abbrev wiredCircuit (trees : Frame (BatchPins n g n r d) Unit) :=
  Prewire.circuit (projection (Function.uncurry (source G))) (verifier d trees)

/-- The same named parse-count wires inside the new joint private input domain. -/
noncomputable abbrev wiredWeight (j : WeightSites n g r d) : Edge ⊕ (RawPin n g r d ⊕ AuxPin n g r d) :=
  .inr (weightedPin j)

/-- The concrete bounded-degree Boolean equality-fanout layout that is routed. -/
noncomputable abbrev wiredLayout (trees : Frame (BatchPins n g n r d) Unit) :=
  BooleanLayout.layout (wiredCircuit G d trees) (wiredWeight (Edge := Edge) d)

/-- Fine input network in the dimension of the selected deck embedding. -/
noncomputable abbrev wiredFine (D : ℕ) (trees : Frame (BatchPins n g n r d) Unit) :=
  (wiredLayout G d trees).network.inDimension D

omit [Fintype Edge] in
private theorem slotFit : r*publicWidth G ≤ r*n :=
  Nat.mul_le_mul_left r ((Nat.le_add_right (publicWidth G) inner).trans G.fits)

variable (D q depth : ℕ)
    (order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2)))

/-- The explicitly prescribed cell of a fine site under the full processor-word block stride. -/
noncomputable abbrev finePlace (trees : Frame (BatchPins n g n r d) Unit) :=
  (wiredFine G d D trees).slotPlace finProdFinEquiv (wiredLayout G d trees).distinct_input_leaves order (r*n) (slotFit G)

/-- The certified routes, with their public width and deck diameter. -/
def WiredRoutes (trees : Frame (BatchPins n g n r d) Unit) : Type :=
  Routed (wiredFine G d D trees) (finePlace G d D q depth order trees)
    (step q (depth+2)) (inverse_letter q (depth+2))
    (endpointBudget (r*n) (batchVolume n r) (Fintype.card (Fin q → Deck (depth+2)))) (q*(1+3*depth^3))

/-- Exact pre-placement query identity for the named tree verifier. -/
def RawQueries (state : Fin g) (trees : Frame (BatchPins n g n r d) Unit) : Prop :=
  ∀ x : Fin r → Fin n → Bool, (queryLayout d trees).network.value
    ((queryLayout d trees).tables (BooleanLayout.factor (verifier d trees) unaryWeight)) (fun ij _ => x ij.1 ij.2) =
    ∏ j, labelQuery d state (x j)

/-- Proof witness retaining the actual tree circuit and routes before any
private literal bits are installed. The original checker serves all raw query words. -/
def WiredWitness (state : Fin g) : Type :=
  {p : (trees : Frame (BatchPins n g n r d) Unit) × WiredRoutes G d D q depth order trees //
    RawQueries d state p.1 ∧ (wiredFine G d D p.1).bitVolume ≤ batchVolume n r}

namespace WiredWitness

variable {G d D q depth order} {state : Fin g} (W : WiredWitness G d D q depth order state)

/-- The shared, unmodified tree verifier stored in the witness. -/
def trees : Frame (BatchPins n g n r d) Unit := W.val.1

/-- Its ordered Cayley paths and congestion certificate. -/
def route : WiredRoutes G d D q depth order W.trees := W.val.2

/-- Its raw integral table identity on every input. -/
theorem computes : RawQueries d state W.trees := W.property.1

/-- The volume of its actual internally wired graph. -/
theorem volume : (wiredFine G d D W.trees).bitVolume ≤ batchVolume n r := W.property.2

end WiredWitness

open private degree_eq from OAI.Computability.BorderVNP.PackedGridLanes

private theorem trivalent_degree {P : Type} [Fintype P] {D : ℕ} (N : Network D P (fun _ => 1)) (tri : N.Trivalent)
    (v : N.Site) : (Finset.univ.filter fun e => N.src e = v).card + (Finset.univ.filter fun e => N.dst e = v).card ≤ 3 := by
  apply le_trans _ (tri.2 v)
  rw [degree_eq N v]
  exact Nat.le_add_right _ _

/-- The prewired mathematical template admits the concrete fine checker and
ordered routes with the full literal slot capacity and the certified volume. -/
theorem exists_wiredWitness (state : Fin g) (s : ℕ) (hn : n = d.val+1) (hg : g ≤ 2*n+s+1)
    (hr : (n+s+2)^24 ≤ r) (hedge : Fintype.card Edge ≤ r*inner) :
    Nonempty (WiredWitness G d D q depth order state) := by
  obtain ⟨trees,compute,size,_⟩ := batched_queries d state hn hg hr
  let M := wiredFine G d D trees
  have hvol : M.bitVolume ≤ batchVolume n r :=
    (rewire_volume (Function.uncurry (source G)) (verifier d trees) (weightedPin (d := d))
      (card_public_private_le G hedge)).trans size
  have hs : Fintype.card M.Site ≤ batchVolume n r :=
    (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hvol)
  have ht : M.Trivalent := BooleanLayout.trivalent (wiredCircuit G d trees) (wiredWeight (Edge := Edge) d)
  obtain ⟨rt⟩ := routed_public_slots (step q (depth+2)) finProdFinEquiv order M
    (wiredLayout G d trees).distinct_input_leaves (r*n) (slotFit G) (inverse_letter q (depth+2))
    hs (trivalent_degree M ht) (short_words q depth)
  exact ⟨⟨⟨trees,rt⟩,compute,hvol⟩⟩

namespace WiredWitness

variable {G d D q depth order} {state : Fin g} (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {Gadget : Type}

/-- The hidden fine bits of this witness, one bundle of private routed wires per cell. -/
abbrev Hidden := PrivateAssignments position W.route

/-- The canonical private unary entries of the named fine verifier. -/
noncomputable abbrev fineTags :
    (wiredFine G d D W.trees).Tables (Diagonal.CellEntries.Entry (GrammarLabel (Fin n × Bool) (Fin g) n) Gadget) :=
  BooleanLayout.powerTags (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d)

/-- The distinct fine weight vertices, with their true incoming occurrence wire. -/
noncomputable def finePowerSites : PowerSites Unit _ Gadget (Nat.clog 2 (r*(2*d.val+1)+1))
    (wiredFine G d D W.trees) W.fineTags :=
  let p := BooleanLayout.powerSites (Gadget := Gadget) (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d)
  ⟨p.site,p.named,p.other⟩

/-- The actual public grid of the fixed private route. -/
noncomputable abbrev seedGrid :=
  (wiredFine G d D W.trees).cayleyGrid (finePlace G d D q depth order W.trees) position (step q (depth+2))
    (cableWidth (Fin q → Deck (depth+2)) (endpointBudget (r*n) (batchVolume n r) (Fintype.card (Fin q → Deck (depth+2))))
      (q*(1+3*depth^3)))

/-- Its layout equals the public field and cable directory on the fixed full slot stride. -/
theorem seedGrid_eq : W.seedGrid position = wiredGrid G q depth order position :=
  grid_eq_public_slots position (step q (depth+2)) finProdFinEquiv order (wiredFine G d D W.trees)
    (wiredLayout G d W.trees).distinct_input_leaves (r*n) (slotFit G) _ _

/-- At fixed hidden bits, the cell reads precisely the subdivided, conditioned
fine tags on its actual padded crossing channels. -/
noncomputable abbrev seedTags (z : W.Hidden position) :
    (W.seedGrid position).Tables (Diagonal.CellEntries.Entry (GrammarLabel (Fin n × Bool) (Fin g) n) Gadget) :=
  privateGridTags position W.route (fun _ => le_rfl) W.fineTags z

/-- One named exponent occurrence at its actual host cell, read from that cell's
private wires or crossing slices as prescribed by the specific route. -/
noncomputable abbrev seedWords (z : W.Hidden position) :
    PowerWords Unit _ Gadget (Nat.clog 2 (r*(2*d.val+1)+1)) (W.seedGrid position) (W.seedTags position z) :=
  privateGridWords position W.route (fun _ => le_rfl) W.finePowerSites z

/-- Concrete public cell name of the fine unary vertex. Different unary
positions can be stored in the same cell. -/
theorem seedWords_site (z : W.Hidden position)
    (w : Unit × WeightSites n g r d) :
    (W.seedWords (Gadget := Gadget) position z).site w =
      finePlace G d D q depth order W.trees (BooleanLayout.weightSite
        (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) w.2) := rfl

end WiredWitness
end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
