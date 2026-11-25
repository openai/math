import OAI.Computability.BorderVNP.PackedFrozenSeedInputs
import OAI.Computability.BorderVNP.PackedHistoryBoxErasure
import OAI.Computability.BorderVNP.PackedRoutingPlaced

/-! # The actual original and grouped source addresses of the signed profile return

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
set_option quotPrecheck false
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

variable (q : (packHistory (plan.frozenLeaf G order position W tag sites edges ports table x) plan.compiled.machine.epoch T).Index)
    (dir : Directory.Layout) (sitePos : 0 < (boundaryShape S (d+1) T).sites)
local notation3 (prettyPrint := false) "publicDir" => {dir with sites := tiles, entries := (fan S)^T*tiles}
local notation3 (prettyPrint := false) "state" => ((packHistory leaf plan.compiled.machine.epoch T).term q).val
local notation "offs" => flatOffset (compiledOffset S (d+1)) T
local notation3 (prettyPrint := false) "hosts" => originalDescriptionRows plan.compiled.machine leaf q publicDir rfl order

/-- The static old-row table used by the emitter is exactly the array of
physical rows of the original sites retained by this attained history. -/
theorem frozen_original_pins :
    (@TerminalCells.originalPins ((fan S)^T) tiles (boundaryShape S (d+1) T).sites sitePos offs) =
      (state).rows.site ∘ hosts := by
  funext j
  exact TerminalCells.originalDescription_selector publicDir plan.compiled leaf rfl order (fun _ => rfl)
    ((Boundary.seedState_rows S G d order position copies table geometry).1) q sitePos j

variable {R m₂ C d₂ k₂ w₂ : ℕ} {Z : Type} [Fintype Z] (F : Packing.CellAddressCircuit.Fields (boundaryShape S (d+1) T).sites m₂
    ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) C d₂ k₂ w₂ Z)
    (z : Z → Bool) (origin : ℕ) (mem : ℕ → ℕ)

local notation "port" => (finProdFinEquiv : FreeBlock R tiles ≃ Fin ((R+1)*tiles)).toEmbedding

/-- The runtime writer receives the real old sites and all actual grouped
ports from the same native output; coordinates of the live source are the
row-major pair of the team and its original grid tile. -/
theorem frozen_routing_image
    (source : RoutingOutputs.Image F (@TerminalCells.originalPins ((fan S)^T) tiles _ sitePos offs) id z origin mem) :
    let live := Function.Embedding.refl (Fin (R+1) × Fin tiles)
    RoutingOutputs.Image F ((state).rows.site ∘ hosts) (port ∘ live ∘ finProdFinEquiv.symm) z origin mem := by
  intro live
  rw [←plan.frozen_original_pins G order position W tag sites edges ports table x q dir sitePos]
  have same : (port ∘ live ∘ finProdFinEquiv.symm) = id := by funext a; exact finProdFinEquiv.apply_symm_apply a
  rwa [same]

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
