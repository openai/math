import OAI.Computability.BorderVNP.PackedSelectedEpochNodeFrames

/-! # Cable capacity of the actual selected seeded public stage -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch Shortening Shortening.StaticRows Packing EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
variable {start T : ℕ} (deep : S.floor+1+S.drop*T ≤ start) {t : ℕ} (ht : t<T)

include deep ht in
/-- The saved cable rectangle contains exactly the statically allocated retained and seed slots. -/
theorem tapeEdgeRectangle (i : Fin S.rounds) :
    (before S start t (i.val+1)).edges = edgeCapacity e (S.fanIn*(before S start t i.val).edges)
      (Fintype.card (PublicDenseReceipt.Seed (S.source.pattern i).bins
        (S.source.asPath.depth S.last (S.high (offset S start t)) (i.val+1)))) := by
  change _ = edgeCapacity e _ (S.source.stageSeeds S.last (S.high (offset S start t)) i)
  rw [stageSeeds_offset S deep ht i,before_next]
  rfl

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
