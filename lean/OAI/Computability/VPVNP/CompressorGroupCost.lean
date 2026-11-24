import OAI.Computability.VPVNP.CompressorDeterministicGroup

/-! # Communication charges across a source-group split

Each source report and each descriptor row is charged once. A bound on the
full native pass therefore covers its two deterministic intervals and its
selected row at the same rate.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace

open BurstRAM BlockPlanner

variable {w : ℕ}

/-- Concatenating source groups adds their report and descriptor charges. -/
theorem groupCost_append (A : Script) (xs ys : List (SourceOnline.Packet A w)) :
    groupCost A (xs++ys) = groupCost A xs + groupCost A ys := by
  simp only [groupCost,List.flatMap_append,RAMBuckets.cost_append,List.length_append,Nat.add_mul]
  ac_rfl

/-- Exact charge of a selector together with its forced prefix and suffix. -/
theorem groupCost_split_selector (A : Script) (before : List (SourceOnline.Packet A w))
    (selected : SourceOnline.Packet A w) (tail : List (SourceOnline.Packet A w)) :
    groupCost A (before++selected::tail) = groupCost A before + groupCost A [selected] + groupCost A tail := by
  change groupCost A (before++([selected]++tail)) = _
  rw [groupCost_append,groupCost_append,Nat.add_assoc]

end CompressorRecords.ScheduledTrace

end VPVNP
end Computability
end OAI
