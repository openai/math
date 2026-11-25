import OAI.Computability.BorderVNP.PackedHistoryNormalizedOuter
import OAI.Computability.BorderVNP.PackedEnrichedEpochRecords

/-! # The admissible assigned boundary of the compiled site epochs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing Catalog Adaptive PublicCapacity
open Shortening.PublicSegments Shortening.PublicRelative Shortening.PreparedBins
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- All boundary route columns at the actual outer depth, including holes and active moves. -/
noncomputable abbrev Pins (start : ℕ) (shape : ℕ → Shape) (w t : ℕ) :=
  RouteRows.Pins (allowedMoves (Cube D) S.budget) (Fintype.card (Cube D)) (depth S start t+1)
    (shape t).sites (shape t).edges w

variable {S} {start : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {shape : ℕ → Shape} {w : ℕ}

/-- The actual assigned route columns and the expanded physical record cap on each tile.
The witness keeps the same prior and payload fields when this pack enters a subdivision. -/
structure Good (budget : ℕ → ℕ) (t : ℕ) (a : State S start P bits shape (Pins S start shape w) t) : Prop where
  ready : RouteRows.Ready (factorEnum D) a.pack a.route a.rows a.dummy a.words
  expanded : ∃ r : RecordData a.pack.layout, ∀ tile, localRecords a.pack.layout true r.prior r.payload
    (fun v => reduceMove (depth S start t) (a.route.origin v) = tile) ≤ budget t

variable {budget : ℕ → ℕ} {t T : ℕ} (deep : S.floor+1+S.drop*T ≤ start)
    (ht : t<T) (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t)

/-- Actual incoming fields, at the starting level used in the inner site execution. -/
theorem inputFields :
    ∃ fields : ∀ i, RecordData (c i).val.pack.layout, ∀ i tile, localRecords (c i).val.pack.layout true
      (fields i).prior (fields i).payload
      (fun v => reduceMove (S.high (offset S start t)) ((routes deep ht c i).origin v) = tile) ≤ budget t := by
  choose fields within using fun i => (c i).property.expanded
  refine ⟨fields,fun i => ?_⟩
  let r := (c i).val.route
  let h := (levels S deep ht).2.2.symm
  exact RecordData.transfer_site_cap h.symm rfl (reindexRoutes_heq h r) (fields i) true (budget t) (within i)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
