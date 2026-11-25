import OAI.Computability.BorderVNP.DiagonalSignedSewnWidth
import OAI.Computability.BorderVNP.DiagonalSelectedRawWriterRoom
import OAI.Computability.BorderVNP.PackedFrozenSeedInputs
import OAI.Computability.BorderVNP.DiagonalEnrichedTape

/-! # The chosen signed seed pays the native label scanner on its actual public history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Branch Crossing Cover Shortening Shortening.Adaptive Packing PhysicalEpochs Packing.DeckGrid
open Diagonal Diagonal.CellEntries Diagonal.ExternalSew GridHosts TeamContraction TeamScales EnrichedOuter
open ParseBatch ParseBatchVerifier Prewire VPVNP BorderVNP.Epoch BorderVNP.Epoch.Round
open ResidueIndex ResidueBox
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 6500
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K]
    {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r k pins link a regs w ec width s copies T d header Q : ℕ} (plan : SeedPlan S (k+1) r d T copies header Q)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs w ec width ≤ k+1)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => tileCount (Fintype.card (Cube D)) d
local notation "G₀" => tapeTemplate p fit pins
variable {order : Fin (tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (siteID : (W.routedFine position).Site ↪ Fin ns) (edgeID : (W.routedFine position).Edge ↪ Fin ne)
    (portID : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
    {σ : Type} [Fintype σ] (x : σ → Bool)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies=R+1)
local notation "M" => plan.compiled.machine
local notation "leaf" => plan.frozenLeaf G₀ order position W code siteID edgeID portID table x

local notation3 (prettyPrint := false) "geom" => (plan.execute G₀ order position σ).choose.eval x

variable {X c : ℕ} (widths : plan.SewnWidths count link X (1/2))
    (q : (packHistory (plan.frozenLeaf (tapeTemplate p fit pins) order position W code siteID edgeID portID table x)
      plan.compiled.machine.epoch T).Index)
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin c)
local notation3 (prettyPrint := false) "net" => EnrichedTape.network (pins:=pins) p fit position free count M leaf rfl q
local notation3 (prettyPrint := false) "state" => ((packHistory leaf (M).epoch T).term q).val
local notation3 (prettyPrint := false) "cell" => fun v : (net).Site => number (reduceMove (depth S (d+1) T) ((state).route.origin v))

include widths in
/-- Integral width of the real numbered-cell network, after installing any late private
literals on the signed template and selecting any path back to the frozen initial state. -/
theorem frozen_signed_intercell_width : intercellWidth net cell ≤ (R+1)*X := by
  let tile (v : (net).Site) := reduceMove (depth S (d+1) T) ((state).route.origin v)
  have ren : intercellWidth net cell = intercellWidth net tile := by
    unfold intercellWidth
    congr 1
    funext edge
    exact propext (not_congr number.injective.eq_iff)
  rw [ren]
  exact (widths G₀ order position table geom (leaf).property q).2.2 le_rfl

include widths in
/-- All intermediate arithmetic of the candidate label program is in range
when fed the actual numbered sewn network used by the terminal writer. -/
theorem frozen_signed_label_envelope {ar : RoutingISA.CubeArena.Layout} {dir : Directory.Layout}
    {w₀ next profile gates outs field : ℕ}
    (room : SelectedRawWriterRoom ar dir w₀ X next profile gates outs field) (teams : dir.teams = R+1) :
    BorderVNP.Cube.LabelIndex.wordEnvelope ar.alphabet
      (intercellWidth net cell+dir.teams*((dir.fields+1)*(dir.processors*dir.literal))) < 2^w₀ := by
  apply room.labels
  rw [teams]
  have cap := plan.frozen_signed_intercell_width p fit W position code siteID edgeID portID table x free
    count widths q number
  exact cap.trans (Nat.mul_le_mul_right X (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)))

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
