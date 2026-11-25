import OAI.Computability.BorderVNP.DiagonalExternalSewNumericName
import OAI.Computability.BorderVNP.PackedHistoryScheduleBudget

/-! # The grouped deck grid at the initial schedule boundary -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover Epoch Packing Shortening.PublicCapacity Diagonal.ExternalSew

/-- At depth zero the schedule allocates exactly the site and cable rows of the grouped grid. -/
theorem gridShape_zero {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}
    (S : SiteSchedule e) (gridDepth : ℕ) :
    SelectedSchedule.boundary S (gridDepth + 1) 0 =
      RowTrace.bottomShape (Fintype.card (Cube D)) gridDepth := by
  simp only [SelectedSchedule.boundary, epochRows, SelectedSchedule.bottom, RowTrace.bottomShape,
    CoverScale.sites, GridHosts.tileCount, Fintype.card_fun, Fintype.card_fin]

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
