import OAI.Computability.BorderVNP.PackedGridAlive

/-! # Successful seed terms are precisely the passing physically stored rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse Diagonal.CellEntries
open scoped Classical
variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
    {Cell Q : Type} [Fintype Cell] [DecidableEq Cell]
    (cell : N.Site → Cell) (position : Cell → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (hidden : ∀ i, N.InsideAssignment cell i) {src dst : Q → Cell} {H : ℕ}
    (packing : (N.cellNetwork cell position).ChannelPacking src dst H)
    {m n : ℕ} (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- Every site of a given cell reads the correct sparse descriptor from the same
physical assignment slab. -/
theorem accepts_cellRead (rules : ∀ v, Rule N v) (c : Cell) (v : {v : N.Site // cell v = c})
    (a x) (bank : ℕ → Bool) (off copy : ℕ)
    (aligned : ∀ i, bank (off+i.val) = physicalBits cell position hidden packing edgeID portID c a x i) :
    accepts N cell c edgeID portID v bank off copy (rules v.val) =
      cellRead cell position hidden packing (guard rules (fun p => bank (p.atBit copy 0))) c v a x := by
  rcases v with ⟨v,rfl⟩
  exact accepts_ownerRead cell position hidden packing edgeID portID rules v a x bank off copy aligned

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
noncomputable local instance aliveDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _

/-- Survival of the chosen term of the actual prewired seed grid is equivalent
to zero at every unused cable lane and success of every Boolean base guard. -/
theorem seed_alive (z : W.Hidden position) (c a x) :
    W.seedTags (Gadget := Gadget) position z c a x ≠ 0 ↔
      padOK (routedPacking position W.route (fun _ => le_rfl)) c a x ∧
      ∀ v, cellRead (cell position W.route) position z (routedPacking position W.route (fun _ => le_rfl))
        (baseTable (W.routedRules position report)) c v a x = true := by
  apply cell_alive _ _ _ _ _ _
  apply routed_alive
  intro v read
  have ha := verifier_alive (Gadget := Gadget) (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) report v read
  unfold originalRule
  cases h : verifierRule (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) BooleanLayout.powerWeight report v <;>
    rw [h] at ha <;> exact ha

/-- When the report lanes are assigned to the true unary bits, the seed term
survives exactly when every actual full sparse site check and padding check passes. -/
theorem seed_alive_checked (z : W.Hidden position) (use : Port → Bool) (c a x)
    (correct : ∀ v, cellRead (cell position W.route) position z (routedPacking position W.route (fun _ => le_rfl))
      (reportTable (W.routedRules position report) use) c v a x = true) :
    W.seedTags (Gadget := Gadget) position z c a x ≠ 0 ↔
      padOK (routedPacking position W.route (fun _ => le_rfl)) c a x ∧
      ∀ v, cellRead (cell position W.route) position z (routedPacking position W.route (fun _ => le_rfl))
        (guard (W.routedRules position report) use) c v a x = true := by
  apply (W.seed_alive (Gadget := Gadget) position report z c a x).trans
  exact and_congr_right' (cell_checks (W.routedRules position report) (cell position W.route) position z
    (routedPacking position W.route (fun _ => le_rfl)) use c a x correct).symm

/-- The same exact criterion on the sparse verifier's physical bank, at arbitrary
copy and offset. It applies before any gadget coefficients are specialized. -/
theorem seed_alive_bank (z : W.Hidden position) {m p : ℕ} (edgeID : (W.routedFine position).Edge ↪ Fin m)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p) (bank : ℕ → Bool) (off copy : ℕ) (c a x)
    (aligned : ∀ i, bank (off+i.val) = physicalBits (cell position W.route) position z
      (routedPacking position W.route (fun _ => le_rfl)) edgeID portID c a x i)
    (correct : ∀ v, cellRead (cell position W.route) position z (routedPacking position W.route (fun _ => le_rfl))
      (reportTable (W.routedRules position report) (fun p => bank (p.atBit copy 0))) c v a x = true) :
    W.seedTags (Gadget := Gadget) position z c a x ≠ 0 ↔
      padOK (routedPacking position W.route (fun _ => le_rfl)) c a x ∧
      ∀ v, accepts (W.routedFine position) (cell position W.route) c edgeID portID v bank off copy
        (W.routedRules position report v.val) = true := by
  apply (W.seed_alive_checked (Gadget := Gadget) position report z _ c a x correct).trans
  exact and_congr_right' (forall_congr' fun v => (congrArg (· = true)
    (accepts_cellRead (cell position W.route) position z (routedPacking position W.route (fun _ => le_rfl))
      edgeID portID (W.routedRules position report) c v a x bank off copy aligned)).symm.to_iff)

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
