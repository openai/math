import OAI.Computability.VPVNP.RAMRecordBlocks

/-!
# Word bounds for burst RAM records

The address of a probe is already a word. Its starting cost and ordinal are
bounded by the total cost of the calls, including the one unit charged per
call. Initialization at site `a` uses `a` for both address and timestamp.
These bounds hold throughout every permutation of the padded input blocks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMMemory

variable {w : ℕ}

/-- All three natural-valued fields of an occupied record fit in words. -/
def RecordFitsWord (r : Record (Word w)) : Prop :=
  r.address < 2 ^ w ∧ r.startCost < 2 ^ w ∧ r.ordinal < 2 ^ w

theorem eventRecords_bounds {start j : ℕ} {es : List (Event w)} {r : Record (Word w)}
    (hr : r ∈ eventRecords start j es) :
    r.address < 2 ^ w ∧ r.ordinal < j + countProbes es := by
  induction es generalizing j with
  | nil => simp [eventRecords] at hr
  | cons e es ih =>
    cases e with
    | tick | choice => exact ih hr
    | read a v | write a v =>
      rcases List.mem_cons.mp hr with rfl | ht
      · exact ⟨a.isLt, by change j < j + (1 + countProbes es); omega⟩
      · simpa only [countProbes, Nat.add_assoc] using ih ht

/-- The start and ordinal of a chronological probe are jointly bounded by the
ending cost. This estimate holds even for the final call at the budget cap. -/
theorem probeRecords_bounds {start : ℕ} {rs : List (Report w)} {r : Record (Word w)}
    (hr : r ∈ probeRecords start rs) :
    r.address < 2 ^ w ∧ r.startCost + r.ordinal < start + RAMBuckets.cost Report.probes rs := by
  induction rs generalizing start with
  | nil => simp [probeRecords] at hr
  | cons s rs ih =>
    rcases List.mem_append.mp hr with hs | ht
    · obtain ⟨ha, hj⟩ := eventRecords_bounds hs
      have he := (mem_eventRecords hs).2.1
      refine ⟨ha, ?_⟩
      simp only [RAMBuckets.cost, Report.probes, he]
      omega
    · simpa only [RAMBuckets.cost, Nat.add_assoc] using ih ht

theorem probeRecords_fitsWord {start : ℕ} {rs : List (Report w)} {r : Record (Word w)}
    (hcost : start + RAMBuckets.cost Report.probes rs ≤ 2 ^ w)
    (hr : r ∈ probeRecords start rs) : RecordFitsWord r := by
  obtain ⟨ha, ht⟩ := probeRecords_bounds hr
  exact ⟨ha, by omega, by omega⟩

theorem initialRecords_fitsWord (header : ℕ → Word w) {S : ℕ} {r : Record (Word w)}
    (hS : S ≤ 2 ^ w) (hr : r ∈ initialRecords S header) : RecordFitsWord r := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
  have h := (List.mem_range.mp ha).trans_le hS
  exact ⟨h, h, Nat.two_pow_pos w⟩

theorem canonicalRecordBlocks_fitsWord (header : ℕ → Word w) {S H : ℕ} {rs : List (Report w)}
    {r : Record (Word w)} (hH : 0 < H) (hcap : RAMBuckets.cost Report.probes rs ≤ S * H)
    (hword : S * H < 2 ^ w) (hr : some r ∈ (canonicalRecordBlocks header S H rs).flatten) :
    RecordFitsWord r := by
  have hp := canonicalRecordBlocks_perm header hcap
  have hm := hp.mem_iff.mpr (List.mem_filterMap.mpr ⟨_, hr, rfl⟩)
  rcases List.mem_append.mp hm with hi | ht
  · exact initialRecords_fitsWord header ((Nat.le_mul_of_pos_right S hH).trans hword.le) hi
  · exact probeRecords_fitsWord (by simpa only [Nat.zero_add] using hcap.trans hword.le) ht

/-- Every occupied slot still fits in words after any sorting-network permutation. -/
theorem perm_canonicalRecordBlocks_fitsWord (header : ℕ → Word w) {S H : ℕ}
    {rs : List (Report w)} {out : List (Option (Record (Word w)))} {r : Record (Word w)}
    (hH : 0 < H) (hcap : RAMBuckets.cost Report.probes rs ≤ S * H) (hword : S * H < 2 ^ w)
    (hp : (canonicalRecordBlocks header S H rs).flatten.Perm out) (hr : some r ∈ out) :
    RecordFitsWord r :=
  canonicalRecordBlocks_fitsWord header hH hcap hword (hp.mem_iff.mpr hr)

end BurstRAM

end VPVNP
end Computability
end OAI
