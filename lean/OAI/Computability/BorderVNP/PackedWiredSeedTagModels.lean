import OAI.Computability.BorderVNP.PackedGridSeedTagRead
import OAI.Computability.BorderVNP.PackedBankWiredSeedState
import OAI.Computability.BorderVNP.DiagonalEnrichedInstalledTags

/-! # The initial grouped seed models every tagged term in the selected history

The finite-port enumeration changes at the initial epoch. The same native
work predicate and tagged observations are read at the actual returned edge
rows and the original tile ordinals.
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

/-- Use the same deck-site equality as the original sparse seed checker. -/
noncomputable local instance tagModelsDeckEq {q l : ℕ} : DecidableEq (Fin q → Deck (l+2)) := Classical.decEq _

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount (Fintype.card (Cube D)) d
local notation "channels" => Shortening.PublicCapacity.Rows.edge (groupedGridRows G axes d order position copies)
local notation "groups" => Equiv.toEmbedding (Equiv.refl (Fin tiles))
local notation "L₀" => seedBundle G axes d order position copies

variable {Gadget : Type} (number : Gadget ↪ ℕ) (z : Fin copies → W.Hidden position)
local notation3 "tags" => (W.bundle (Gadget := Gadget) position copies z).tags
local notation3 "pred" => fun c => W.seedBirthPredicate position tag siteID edgeID portID c z

omit [NeZero D] in
/-- All the sparse programs installed on the grouped source grid model the
true bundled tags on the original row-major cable and port order. -/
theorem wiredSeedPrograms_tagModels :
    TagModels L₀ channels groups (wiredSeedPrograms W position tag siteID edgeID portID copies)
      tags number pred := by
  intro c a x
  exact ⟨W.seedTagRead position tag siteID edgeID portID channels groups c number z a x⟩

open BorderVNP.Epoch.Round
attribute [local instance] portFintype

variable {w : ℕ} (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K)
    (words : Pins S (d+1) (SelectedSchedule.boundary S (d+1)) w 0 → Bool)

local notation3 (prettyPrint := false) "a₀" => seedState S G d order position copies table words
local notation3 "states" => wiredSeedStatePrograms S W position tag siteID edgeID portID copies table words

/-- The saved initial machine, including its actual returned row names and
layer-zero finite-port enumeration, reads every hidden tuple correctly. -/
theorem wiredSeedStatePrograms_tagModels :
    TagModels (a₀).pack.layout (a₀).rows.edge groups states tags number pred := by
  let outer := portFintype (k := fan S) (b := 0) (P := Fin tiles)
  have actual := wiredSeedPrograms_tagModels W position tag siteID edgeID portID copies number z
  have changed := TagModels.changePrivate (Fin.fintype tiles) outer L₀ channels groups
    (wiredSeedPrograms W position tag siteID edgeID portID copies) tags number pred actual
  exact @TagModels.renumber _ _ _ _ outer _ _ _ L₀ channels groups states tags number pred _ _ changed (a₀).rows.edge groups
    (congrArg Shortening.PublicCapacity.Shape.edges (gridShape_zero S d)) rfl
    (seedState_rows S G d order position copies table words).2 (fun _ => rfl)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
