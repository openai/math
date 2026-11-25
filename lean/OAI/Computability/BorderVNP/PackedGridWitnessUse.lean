import OAI.Computability.BorderVNP.PackedGridRoutedUse
import OAI.Computability.BorderVNP.ParseBatchWiredWitness

/-! # Reading a named exponent bit at its actual prewired seed-grid cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse Diagonal.CellEntries
open scoped Classical
variable {D : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}

/-- Read one named local wire or external lane from its actual site incidence. -/
def readLane (v : N.Site) (a : ∀ e : {e : N.Edge // N.src e = v ∨ N.dst e = v}, Fin (N.width e.val) → Bool)
    (x : ∀ p : {p : P // N.attach p = v}, Fin (bits p.val) → Bool) : CellBox.Lane N v → Bool
  | .inl ⟨e,k⟩ => a e k
  | .inr ⟨p,k⟩ => x p k

/-- The Boolean table tested by a sparse rule at each fine site. -/
def guard (rules : ∀ v, Rule N v) (use : Port → Bool) : N.Tables Bool :=
  fun v a x => (rules v).passes (readLane v a x) use

/-- Changing embedding dimension preserves every truth table and unary lane. -/
def Rule.inDimension (D' : ℕ) {v : N.Site} : Rule N v → Rule (N.inDimension D') v
  | .truth f => .truth f
  | .unary l p => .unary l p

/-- At the same physical assignment, the dimension change preserves successful checks. -/
theorem Rule.passes_inDimension (D' : ℕ) {v : N.Site} (r : Rule N v) (read use) :
    (r.inDimension D').passes read use = r.passes read use := by cases r <;> rfl

variable {Cell Q : Type} [Fintype Cell] [DecidableEq Cell] [Fintype Q]
    (cell : N.Site → Cell) (position : Cell → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (hidden : ∀ i, N.InsideAssignment cell i) {src dst : Q → Cell} {H : ℕ}
    (packing : (N.cellNetwork cell position).ChannelPacking src dst H)

/-- Read an arbitrary fine table at its true owner, restricting the hidden and
public wires to those incident to that fine site. -/
noncomputable def ownerRead {A : Type*} (table : N.Tables A) (v : N.Site)
    (a : {q : Q // src q = cell v ∨ dst q = cell v} → Fin H → Bool)
    (x : ∀ p : {p : P // cell (N.attach p) = cell v}, Fin (bits p.val) → Bool) : A :=
  fineFactor cell table (cell v) (hidden _) ⟨v,rfl⟩
    (fun e i => a ⟨packing.channel e.val, e.property.imp
      ((packing.src_eq e.val).trans) ((packing.dst_eq e.val).trans)⟩ (packing.address ⟨e.val,i⟩).2) x

variable {b : ℕ} {Team Param Gadget : Type} [Fintype Team] [Fintype Param]
    {tags : N.Tables (Entry Param Gadget)} (words : PowerWords Team Param Gadget b N tags)

/-- A passing check on the restricted fine assignment identifies the reported
bit with the public table's selected bit at the corresponding cell. -/
theorem report_at_grid_owner (slot : PowerSlot Team Param b) (check : N.Tables Bool)
    (reported : Bool) (original : ∀ a x, check (words.site slot) a x = true →
      reported = words.selected (words.site slot) a x slot) (a x)
    (hp : conditionedGridTags cell position packing tags hidden (cell (words.site slot)) a x ≠ 0)
    (ok : ownerRead cell position hidden packing check (words.site slot) a x = true) :
    reported = (words.gridWords cell position hidden packing).selected (cell (words.site slot)) a x slot := by
  rw [PowerWords.grid_owner_selected words cell position hidden packing slot a x hp]
  exact original _ _ ok

end Packing.GridBoxes

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes Diagonal.CellEntries GridPlacement Cover TeamContraction
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {Gadget : Type} (report : WeightSites n g r d → Port)

/-- Use the same equality instance as the actual conditioned deck-grid table. -/
noncomputable local instance witnessUseDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _

/-- The sparse rule at an original site of the actual prewired witness. -/
noncomputable def originalRule (v : (wiredFine G d D W.trees).Site) : Rule (wiredFine G d D W.trees) v :=
  (verifierRule (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) BooleanLayout.powerWeight report v).inDimension D

/-- Every actual prewired unary report whose fine-site check passes agrees with
the precise selected bit of the chosen private seed term, for both Boolean values. -/
theorem seed_report (z : W.Hidden position) (j : WeightSites n g r d) (use : Port → Bool) (a x)
    (hp : W.seedTags (Gadget := Gadget) position z ((W.seedWords (Gadget := Gadget) position z).site ((),j)) a x ≠ 0)
    (ok : ownerRead (cell position W.route) position z (routedPacking position W.route (fun _ => le_rfl))
      (guard (routedRule (wiredFine G d D W.trees) (wireRoutes position W.route) (W.originalRule report)) use)
      (.inl ((W.finePowerSites (Gadget := Gadget)).site ((),j))) a x = true) :
    use (report j) = (W.seedWords (Gadget := Gadget) position z).selected ((W.seedWords (Gadget := Gadget) position z).site ((),j)) a x ((),j) := by
  let M := wiredFine G d D W.trees
  let paths := wireRoutes position W.route
  let sites := W.finePowerSites (Gadget := Gadget)
  apply report_at_grid_owner (cell position W.route) position z (routedPacking position W.route (fun _ => le_rfl))
    (sites.subdivision paths).toWords ((),j) _ (use (report j)) _ a x hp ok
  intro wire port passing
  let read : CellBox.Lane (M.subdivide paths) (.inl (sites.site ((),j))) → Bool :=
    readLane _ wire port
  apply report_at_routed_source M paths sites (W.originalRule report) ((),j) (report j) use _ read passing
  intro old good
  let vr := verifierRule (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) BooleanLayout.powerWeight report
    (BooleanLayout.weightSite (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) j)
  have good' : vr.passes old use = true := (Rule.passes_inDimension D vr old use).symm.trans good
  have hn := reported_selected (Gadget := Gadget) (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) report j
    (fun e k => old (.inl ⟨e,k⟩)) (fun p k => old (.inr ⟨p,k⟩)) use
  apply hn
  change vr.passes _ use = true
  convert! good' using 1
  apply congrArg (fun read => vr.passes read use)
  funext l
  rcases l with ⟨e,k⟩ | ⟨p,k⟩ <;> rfl

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
