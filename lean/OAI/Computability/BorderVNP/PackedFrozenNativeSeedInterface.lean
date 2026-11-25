import OAI.Computability.BorderVNP.PackedFrozenNativePort
import OAI.Computability.BorderVNP.PackedFrozenNativeFrames
import OAI.Computability.BorderVNP.PackedFrozenSeedFormatSize

/-! # The measured chronological history of one physical seed plan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.Inherited.WorkWords Packing.Inherited.FrozenTape
open Diagonal Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire
open TeamScales Filter EnrichedOuter VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1900000
set_option maxRecDepth 6000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
local notation "axes" => Fintype.card (Cube D)

/-- The numeric native budget on the physical finite grid. The same chosen
plan and its same stages work for every actual public wiring, coordinate
order and bottom circuit. -/
def SeedPlan.TapeWithin {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    (wr : WidthRanges S (d+1) T (60*logWidth r n)) (hm : 0 < m) : Prop :=
  let w := 60*logWidth r n
  let V := CoverScale.sites (Cube D) (d+1)
  let hdr := grouped V (copies*GridHosts.inputBlockWidth r n axes d)
  let port := (finCongr (seedPortCount (D:=D) d)).toEmbedding
  ∀ {teams time pins link inner : ℕ} {Edge : Type} (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount axes d) ≃ (Fin axes → Deck (d+2)))
    (position : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {σ : Type} [Fintype σ] (f : Frame σ (Boundary.Pins S (d+1) (boundary S (d+1)) w 0)), f.size ≤ 2 →
    let fmt := Boundary.seedFormat G order position copies
    let source := Boundary.seedTapeFrame S plan G order position f
    ((Q*(compile (plan.compiled.tapeSteps fmt hdr port wr hm) T le_rfl (repeatLeaf (fan S) source T)).size+
      Fintype.card (Slot (fan S) (Machine.Guess S (d+1) (fun _ _ => w)) T) : ℕ) : ℝ) < r*(n:ℝ)^(92/100:ℝ)

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
