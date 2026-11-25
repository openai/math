import OAI.Computability.BorderVNP.PackedHistoryNormalizedCompilation
import OAI.Computability.BorderVNP.PackedHistoryNormalizedMachine
import OAI.Computability.BorderVNP.PackedSelectedScheduleRanges

/-! # All enriched epochs on the chosen processor rectangles

A fixed schedule determines every inner and outer row range. The compiled
node families for those very ranges retain the selected physical histories,
their assigned pin vectors and the measured costs at each boundary.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Adaptive Packing PublicCapacity
open Diagonal TeamScales Filter EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The actual allocated rectangle at every outer boundary of this schedule. -/
noncomputable abbrev boundaryShape (start : ℕ) := epochRows e S.fanIn S.rounds (interiors S)
  (seedCount S start) (bottom (D := D) start)

/-- The two boundary rectangles both fit the chosen processor word width.
The first and last actual inner stages witness these two inequalities. -/
theorem boundary_fits {r n start t : ℕ} {den cut : Fin S.rounds → ℕ}
    (range : ∀ i : Fin S.rounds, Ranges S r n start t i (den i) (cut i)) :
    ((boundaryShape S start t).subdivide (interiors S)).sites ≤ 2^(60*logWidth r n) ∧
      (boundaryShape S start (t+1)).sites ≤ 2^(60*logWidth r n) := by
  let first : Fin S.rounds := ⟨0,S.rounds_pos⟩
  let last : Fin S.rounds := ⟨S.rounds-1,by have := S.rounds_pos; omega⟩
  have hfirst := (range first).words.2.2.2.1
  have hlast := (range last).words.2.2.2.2.2.2.1
  constructor
  · exact (Nat.le_mul_of_pos_left _ S.positiveFanIn).trans hfirst
  · have h : last.val+1 = S.rounds := by change S.rounds-1+1 = S.rounds; have := S.rounds_pos; omega
    change (before S start t (last.val+1)).sites ≤ _ at hlast
    rw [h] at hlast
    exact hlast

variable {S} {P : Type} [Fintype P] (bits : P → ℕ) {start T : ℕ}
    (deep : S.floor+1+S.drop*T ≤ start) (budget : ℕ → ℕ) (cap : ℕ → ℕ → ℕ) (w : ℕ)

local notation "height" => fun t => S.high (offset S start t)
local notation "siteSlots" => fun t j => Shape.sites (before S start t j)
local notation "edgeSlots" => fun t j => Shape.edges (before S start t j)
local notation "outerRows" => boundaryShape S start

/-- Source compilation data for all active epochs on the allocated processor.
Each node retains its own literal gate lists, native inner history and physical
input/output row receipts. -/
structure Compiled where
  /-- Canonical nodes for each depth and each internal shortening stage. -/
  nodes : ∀ t, t<T → ∀ i : Fin S.rounds, S.source.Node S.last (height t) (siteSlots t) (edgeSlots t) w S.fanIn i
  /-- Batched subdivision, installed measured nodes, and the minimizing terminal frame. -/
  atLevel : ∀ t ht, Boundary.Compilation (bits := bits) deep ht budget (siteSlots t) (edgeSlots t) (cap t) w
    (show outerRows (t+1) = ⟨siteSlots t S.rounds,edgeSlots t S.rounds⟩ from rfl) (nodes t ht)

variable {bits deep budget cap w} (C : Compiled bits deep budget cap w)

/-- The actual machine on the selected schedule at all active outer levels. -/
noncomputable def Compiled.machine : Machine deep (Boundary.Good (bits := bits) (shape := outerRows) (w := w) budget)
    (fun t => S.source.StatePins S.last (height t) (siteSlots t) (edgeSlots t) w) (fun _ _ => w) :=
  fun t ht => (C.atLevel t ht).epoch

/-- The inner guard and pin allocation of the actual selected outer machine
use exactly the gates of the measured native source node. -/
theorem Compiled.node_size (t : ℕ) (ht : t<T) (i : Fin S.rounds) :
    ((C.machine t ht).step i.val i.isLt).size = (C.nodes t ht i).size :=
  (C.atLevel t ht).step_size i

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
