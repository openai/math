import OAI.Computability.BorderVNP.PackedFrozenProgramSchemas
import OAI.Computability.BorderVNP.PackedFrozenCarryCost
import OAI.Computability.BorderVNP.PackedHistoryNormalizedProcessor
import OAI.Computability.BorderVNP.PackedSelectedEpochNodeFrames

/-! # Fixed cumulative record formats for all physical epochs

A child first receives its subdivision records. The subsequent path has one
complete copy of this child format at each of its leaves. Flattening and the
outer return use the format of the path's root without appending another
record. All types are fixed by the public schedule and capacities.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open Crossing Shortening Shortening.PublicCapacity Cover Epoch PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}
    (S : Normalized.SiteSchedule e) (start w : ℕ)

/-- Full old endpoint/relay block installed separately for each child at the start of an epoch. -/
noncomputable def installed (t : ℕ) (prior : Format) : Format :=
  prior.append (Format.subdivision (boundaryShape S start t).edges (portSlots S start t 0) (interiors S) w)

/-- The public template for this epoch, beginning with one already subdivided child. -/
noncomputable def pathFrom (t : ℕ) (prior : Format) (j : ℕ) : Format :=
  inner S.source S.last (S.high (EnrichedOuter.offset S start t)) S.fanIn (fun i => (before S start t i).edges)
    (portSlots S start t 0) w (installed S start w t prior) j

/-- The cumulative format at each actual outer boundary. The root of the complete inner tree
is also the source tape of the flattened outer return. -/
noncomputable def epoch (base : Format) : ℕ → Format
  | 0 => base
  | t+1 => pathFrom S start w t (epoch base t) S.rounds

/-- Actual inner state format of an epoch entered with the full saved previous history. -/
noncomputable def stage (base : Format) (t j : ℕ) : Format :=
  pathFrom S start w t (epoch S start w base t) j

/-- The original bottom frame supplies exactly this initial format. -/
@[simp] theorem epoch_zero (base : Format) : epoch S start w base 0 = base := rfl

/-- Subdivision is the first chronological append in each of the outer fan's true children. -/
theorem stage_zero (base : Format) (t : ℕ) :
    stage S start w base t 0 = installed S start w t (epoch S start w base t) := rfl

/-- Flattening ports and final outer placement reuse the root format of the attained inner path. -/
theorem epoch_next (base : Format) (t : ℕ) :
    epoch S start w base (t+1) = stage S start w base t S.rounds := rfl

/-- The named nested-port capacity equals the row-major exterior port count of the same schedule. -/
theorem stage_ports (t j : ℕ) : Parallel.nestedCapacity S.fanIn (portSlots S start t 0) j = portSlots S start t j := by
  rw [nested_ports]; simp [portSlots]

/-- Real seed cardinality on an attained epoch, before any histogram is read. -/
theorem stage_seeds {T t : ℕ} (deep : S.floor+1+S.drop*T ≤ start) (ht : t<T) (i : Fin S.rounds) :
    Fintype.card (Seeds S.source S.last (S.high (EnrichedOuter.offset S start t)) i) = seedCount S start t i :=
  stageSeeds_offset S deep ht i

/-- Exact successor format in the physical schedule's child, cable, argument and seed order.
The inherited port count is the named replay's nested capacity, measured by `stage_ports`. -/
theorem stage_next (base : Format) (t : ℕ) (i : Fin S.rounds) :
    stage S start w base t (i.val+1) =
      innerRound S.source S.last (S.high (EnrichedOuter.offset S start t)) S.fanIn
        (fun j => (before S start t j).edges) (portSlots S start t 0) w i
        (stage S start w base t i.val) :=
  inner_next S.source S.last (S.high (EnrichedOuter.offset S start t)) S.fanIn
    (fun j => (before S start t j).edges) (portSlots S start t 0) w
    (installed S start w t (epoch S start w base t)) i

/-- Complete raw public output at a saved outer site/cable boundary. -/
noncomputable abbrev outerPins (base : Format) (t : ℕ) :=
  (epoch S start w base t).Output (EnrichedOuter.Boundary.Pins S start (boundaryShape S start) w t)
    (boundaryShape S start t).sites w w

/-- Complete named inner output, including the two measured per-site widths and all retained records. -/
noncomputable abbrev stagePins (base : Format) (t j : ℕ) :=
  (stage S start w base t j).Output
    (S.source.StatePins S.last (S.high (EnrichedOuter.offset S start t))
      (fun i => (before S start t i).sites) (fun i => (before S start t i).edges) w j)
    (before S start t j).sites w w

/-- Total state dimensions after adding the earlier record chronology to the returned route. -/
theorem outerPins_card (base : Format) (t : ℕ) :
    Fintype.card (outerPins S start w base t) =
      Fintype.card (EnrichedOuter.Boundary.Pins S start (boundaryShape S start) w t) +
      (boundaryShape S start t).sites*(2*w) +
      (Fintype.card (epoch S start w base t).Rows*(1+w)+Fintype.card (epoch S start w base t).Payload) :=
  Format.output_card ..

/-- The actual inputs and outputs of subdivision include all leaves of the inner combining tree. -/
theorem pre_card (base : Format) (t : ℕ) :
    Fintype.card (Fin (EnrichedOuter.fan S) × outerPins S start w base t) =
      S.fanIn^S.rounds * Fintype.card (outerPins S start w base t) ∧
    Fintype.card (Fin (EnrichedOuter.fan S) × stagePins S start w base t 0) =
      S.fanIn^S.rounds * Fintype.card (stagePins S start w base t 0) := by
  simp only [Fintype.card_prod,Fintype.card_fin,EnrichedOuter.fan,true_and]

end Packing.Inherited.FrozenTape.ProgramSchemas

end BorderVNP
end Computability
end OAI
