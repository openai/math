import OAI.Computability.BorderVNP.PackedFrozenSeedInputs
import OAI.Computability.BorderVNP.PackedHistoryBoxErasure

/-! # Resolution of original signed verification boxes in the frozen packet

The static slot ownership uses the row numbers of the selected seed before
the profile is known. The single protected box at each such original slot
is exactly the ordered factor list printed in that seed's private tape.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.DeckGrid Packing.Inherited Packing.PhysicalEpochs Diagonal Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace
open TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar EnrichedOuter TeamScales
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 6500
set_option backward.isDefEq.respectTransparency false

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {n r d T copies header Q : ℕ} (plan : SeedPlan S n r d T copies header Q)
    {teams time pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {σ : Type} [Fintype σ] {g : ℕ} {len : Fin n} {key : Fin g}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order key)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K) (x : σ → Bool)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation3 (prettyPrint := false) "leaf" => plan.frozenLeaf G order position W tag sites edges ports table x
local notation3 (prettyPrint := false) "geometry" => (plan.execute G order position σ).choose.eval x
local notation3 (prettyPrint := false) "seed" => Boundary.seedBirthPrograms S order position W tag sites edges ports table geometry
local notation3 (prettyPrint := false) "channels" => (groupedGridRows G axes d order position copies).edge
local notation "groups" => Equiv.toEmbedding (Equiv.refl (Fin tiles))
local notation3 (prettyPrint := false) "original" v => W.seedStored position tag sites edges ports channels groups v

/-- Every scheduled paid entry and every original pointer, including pointers
with the same bytes on different leaves, resolves to its own ordered boxes
on a genuine public history. All unused destination rows resolve to empty. -/
theorem frozen_signed_boxes_resolved
    (rows : ∀ t ht, (plan.compiled.machine t ht).F.SiteRows) (number : e.Entry → ℕ)
    (q : (packHistory leaf plan.compiled.machine.epoch T).Index) (dir : Directory.Layout)
    (room : 0 < (boundaryShape S (d+1) T).sites) (i : Fin (boundaryShape S (d+1) T).sites) :
    let publicDir := { dir with sites := tiles, entries := (fan S)^T * tiles }
    let bodies := fun j : Fin ((fan S)^T * tiles) => original (order (finProdFinEquiv.symm j).2)
    let final := ((packHistory leaf plan.compiled.machine.epoch T).term q).val
    (scheduledBoxes publicDir rfl number room i).map (CellSparse.Packet.Source.factors bodies) =
      FinalCell.slots final.rows.site (fun v => (plan.compiled.machine.terminalPrivatePrograms rows number leaf seed q v).program.boxes) i := by
  intro publicDir bodies final
  let fine := fun v => (seed v).program.boxes
  let initial := FinalCell.slots (leaf).val.rows.site fine
  have real : BoxRoster.Realizes (leaf).val.rows.site fine initial := by
    constructor
    · intro v
      simp only [initial,FinalCell.slots,Function.partialInv_left (leaf).val.rows.site.injective,Option.elim_some]
    · intro i hole
      have none : Function.partialInv (leaf).val.rows.site i = none := by
        cases h : Function.partialInv (leaf).val.rows.site i with
        | none => rfl
        | some v => exact (hole ⟨v,((leaf).val.rows.site.injective.isPartialInv v i).mp h⟩).elim
      simp only [initial,FinalCell.slots,none,Option.elim_none]
  have named : ∀ j, ((leaf).val.rows.site (order j)).val = j.val := fun j =>
    (Boundary.seedState_rows S G d order position copies table geometry).1 j
  exact scheduledBoxes_resolved publicDir plan.compiled leaf rfl order (fun _ => rfl) named q rows number room seed initial real
    bodies (fun _ => rfl) i

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
