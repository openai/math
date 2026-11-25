import OAI.Computability.BorderVNP.PackedWiredSeedTagModels
import OAI.Computability.BorderVNP.PackedInheritedWorkBottomPrepSeed
import OAI.Computability.BorderVNP.DiagonalExtractedBirthPredicate
import OAI.Computability.BorderVNP.DiagonalBottomChoices

/-! # The physical original-digit predicate on the actual initial seed state

The slot/copy/tile choices extracted from raw physical banks are the very
same independent digits that the original tagged seed reads. After the
private choices are transposed into leaf tuples the predicate has no extra
passing, staging or global wire consistency hypothesis.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Cover Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Packing Packing.DeckGrid Packing.PhysicalEpochs
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction GridPlacement Shortening.PreparedBins
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar Inherited BottomGridBank BottomReports DeckGrid.WiredWitness
open Diagonal.CellEntries Inherited.Site.Programs
open scoped Classical
set_option maxHeartbeats 2200000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {R r t pins link inner n g d : ℕ} {Edge : Type} [Fintype Edge] {G : Wiring R r t pins link inner n Edge}
    {len : Fin n} {key : Fin g}
    {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order key)
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (siteID : (W.routedFine position).Site ↪ Fin ns) (edgeID : (W.routedFine position).Edge ↪ Fin ne)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np) (copies : ℕ)

/-- Use the deck-site equality of the routed fine assignments. -/
noncomputable local instance birthChoicesDeckEq {q l : ℕ} : DecidableEq (Fin q → Deck (l+2)) := Classical.decEq _

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount (Fintype.card (Cube D)) d
local notation "groups" => Equiv.toEmbedding (Equiv.refl (Fin tiles))

variable {Gadget : Type} (number : Gadget ↪ ℕ)

open BorderVNP.Cube.Physical.NativeAssignments
open BorderVNP.Epoch.Round
attribute [local instance] portFintype

variable {leaves : ℕ}
local notation3 "slabs" => fun j : Fin leaves × (Fin axes → Deck (d+2)) =>
  W.seedSlab position tag siteID edgeID portID j.2
local notation3 "hidden" z => W.bottomChoicesEquiv position edgeID slabs (fun _ => rfl) z

omit [NeZero D] in
/-- At each original host the named fine-wire predicate equals the physical
offset-zero work predicate extracted before any row or guard was evaluated. -/
theorem seedBirthPredicate_bottomChoices (z : BottomChoices slabs (fun _ => copies))
    (leaf : Fin leaves) (c : Fin axes → Deck (d+2)) (work : ℕ → Bool) :
    W.seedBirthPredicate position tag siteID edgeID portID c ((hidden z) leaf) work ↔
      birthPredicate slabs (fun _ => copies) z (leaf,c) work := by
  unfold DeckGrid.WiredWitness.seedBirthPredicate birthPredicate
  apply forall_congr' fun i => forall_congr' fun k => ?_
  rw [W.bottomChoicesEquiv_read position edgeID slabs (fun _ => rfl) z leaf i c, Equiv.symm_apply_apply]
  rfl

variable (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K)
    (words : Pins S (d+1) (SelectedSchedule.boundary S (d+1)) (60*TeamScales.logWidth r n) 0 → Bool)

local notation3 (prettyPrint := false) "a₀" => seedState S G d order position copies table words

/-- On the actual measured initial program and the true returned incidence
directory, every original leaf models its genuine extracted work choices. -/
theorem seedBirthPrograms_tagModels (z : BottomChoices slabs (fun _ => copies)) (leaf : Fin leaves) :
    TagModels (a₀).pack.layout (a₀).rows.edge groups
      (seedBirthPrograms S order position W tag siteID edgeID portID table words)
      ((W.bundle (Gadget := Gadget) position copies ((hidden z) leaf)).tags) number
      (fun c work => birthPredicate slabs (fun _ => copies) z (leaf,c) work) := by
  have model := wiredSeedStatePrograms_tagModels S W position tag siteID edgeID portID copies number
    ((hidden z) leaf) table words
  have pred : (fun c => W.seedBirthPredicate position tag siteID edgeID portID c ((hidden z) leaf)) =
      fun c work => birthPredicate slabs (fun _ => copies) z (leaf,c) work := by
    funext c work
    exact propext (seedBirthPredicate_bottomChoices W position tag siteID edgeID portID copies z leaf c work)
  exact pred ▸ model

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
