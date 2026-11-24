import OAI.Computability.VPVNP.LiveProgram
import OAI.Computability.VPVNP.LiveOutsideBudget

/-!
# Combining the auxiliary pair charge with the outer live program

The small-o estimate for the compressed pair can be used with constant
one quarter. Dispatch adds at most two probes per pair call. The rest of
the group costs at most one physical processor array. These two estimates
suffice for the total transcript cap, while the two-probe and finite
instruction margins account for every individual dispatch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram

open BurstRAM LiveStageLink

variable {w d : ℕ}

theorem linked_cost_le_three (next : Fin d → Option (Fin d)) (addr : Word w) (s : Fin d)
    (rs : List (Report w)) :
    RAMBuckets.cost Report.probes (rs.map (linkedReport next addr s)) ≤ 3*RAMBuckets.cost Report.probes rs := by
  induction rs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    simp only [List.map_cons, RAMBuckets.cost, linkedReport_probes]
    split <;> omega

/-- The physically charged prefix, linked pair, and suffix all satisfy the
same `withinCaps` condition used by the parsimonious transcript theorem. -/
theorem withinCaps_pair_group {S H : ℕ} (hH : 4 ≤ H)
    (next : Fin d → Option (Fin d)) (addr : Word w) (s : Fin d) (pre pair post : List (Report w))
    (outside : RAMBuckets.cost Report.probes pre + RAMBuckets.cost Report.probes post ≤ S)
    (oneQuarter : 4*RAMBuckets.cost Report.probes pair ≤ S*H)
    (eachOutside : ∀ r ∈ pre ++ post, 1+r.probes ≤ H)
    (eachPair : ∀ r ∈ pair, 3+r.probes ≤ H) :
    withinCaps S H (pre ++ pair.map (linkedReport next addr s) ++ post) := by
  constructor
  · rw [RAMBuckets.cost_append, RAMBuckets.cost_append]
    have h := linked_cost_le_three next addr s pair
    have hS : 4*S ≤ S*H := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left S hH
    omega
  · intro r hr
    rcases List.mem_append.mp hr with h | h
    · rcases List.mem_append.mp h with h | h
      · exact eachOutside r (List.mem_append_left _ h)
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
        rw [linkedReport_probes]
        have := eachPair a ha
        split <;> omega
    · exact eachOutside r (List.mem_append_right _ h)

/-- For the fixed outer table, a pair trace with a finite additive clock
margin executes within the live `n^10000` private-work budget. -/
theorem linked_pair_clock (next : Stage → Option Stage) (addr : Word w) (s : Stage)
    (r : Report w) {n : ℕ} (margin : r.events.length + 48 ≤ n^10000) :
    (linkedReport next addr s r).events.length + 1 ≤ n^10000 := by
  have h := linkedReport_length_le next addr s r
  change (linkedReport next addr s r).events.length ≤ r.events.length+2*21+5 at h
  omega

end LiveProgram

end VPVNP
end Computability
end OAI
