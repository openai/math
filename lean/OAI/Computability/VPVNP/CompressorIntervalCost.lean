import OAI.Computability.VPVNP.CompressorOnlineBranchCut

/-! # Probe costs of online descriptor intervals

Each row contributes its source worker reports and its share of the
calendar, recipe and launch costs. An interval ends at the boundary
immediately after its last row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.Online.Run

open BurstRAM

variable {d initial phases w : ℕ} {C : Catalog d}
local notation "q" => initial + phases

/-- Summing the source workers' costs gives the cost of their concatenated reports. -/
theorem sourceCost_eq_flatMap (steps : List (Step d q w)) :
    sourceCost steps = RAMBuckets.cost Report.probes (steps.flatMap fun s => s.row.reports) := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
    rw [List.flatMap_cons, RAMBuckets.cost_append, ← ih]
    rfl

/-- The dispatcher charges a fixed overhead per scheduled row of the interval. -/
theorem interval_cost_bound (plan : Config C initial phases) (ports : Ports w)
    (steps : List (Step d q w)) (m : Memory w) {cap : ℕ}
    (valid : Interval plan ports cap m steps) :
    RAMBuckets.cost Report.probes (intervalLog plan ports m steps) ≤
      sourceCost steps * (arity C + 3) + steps.length * (maxReads plan + 4 * arity C + 26) := by
  induction steps generalizing m with
  | nil => simp [intervalLog, RAMBuckets.cost, sourceCost]
  | cons s rest ih =>
    obtain ⟨row, tail⟩ := valid
    have tailCost := ih _ tail
    have count : s.row.reports.length ≤ RAMBuckets.cost Report.probes s.row.reports := by
      rw [RAMBuckets.cost_eq_length_add_probes]
      omega
    have params := params_le_arity C s.row.worker
    have overhead := Nat.mul_le_mul count (Nat.add_le_add_right params 2)
    have reads := reads_le plan s.phase
    rw [intervalLog, RAMBuckets.cost_append, row_cost plan ports m s.phase s.row row.source]
    change _ ≤ (RAMBuckets.cost Report.probes s.row.reports + sourceCost rest) * _ +
      (rest.length + 1) * _
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    have workerCost : RAMBuckets.cost Report.probes s.row.reports * (arity C + 3) =
        RAMBuckets.cost Report.probes s.row.reports * (arity C + 2) +
          RAMBuckets.cost Report.probes s.row.reports := Nat.mul_succ ..
    omega

end CompressorRecords.Schedule.Online.Run

end VPVNP
end Computability
end OAI
