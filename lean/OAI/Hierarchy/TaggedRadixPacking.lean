import OAI.Hierarchy.TaggedPhysicalRun
import OAI.Hierarchy.TaggedRadixLayout

namespace OAI
/-! # Packing wide tagged calls into bounded-digit stable radix passes -/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork RadixStage CatalystSubstitution
open Filter
open scoped Classical
noncomputable section

variable {F : Type*} [Field F] {k : ℕ} {a B : ℝ}

/-- The certified physical layout required by the exponent recurrence. -/
theorem packing_layout (ha : 1 < a) (hB : 1 < B) : Layout F k a B := by
  apply layout_of_start_runs ha hB 6000000000000
  filter_upwards [eventual_grid_scales ha hB,eventually_ge_atTop (2:ℕ)] with h grid two
  intro n count cover Y
  apply stage_run two grid _ cover Y
  rw [count]
  exact (grid.passesFor_bounds ha.le).2.1

/-- Width packing for the tagged data predicate with all oracle occurrences,
local arithmetic and the global pack order included. -/
theorem packing_bound : RadixBound F k := radix_bound (fun ha hB => packing_layout ha hB)

end
end Hierarchy.Tagged.Radix

end OAI
