import OAI.Computability.VPVNP.RAMRecords

/-!
# Padded record blocks for the RAM transcript

Each site in Lemma 10.1 contributes one initialization record, the probes of the
calls whose starting costs belong to that site, and enough empty slots to fill
a block of size `4H`. Filtering the physical array to its occupied slots gives
exactly the initialization and probe records, up to permutation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMMemory

variable {w : ℕ}

/-- Fill the slots in a single site. The cost of its first call is supplied
by the predecessor, so probe timestamps are global across sites. -/
def siteRecordBlock (header : ℕ → Word w) (H site start : ℕ) (rs : List (Report w)) :
    List (Option (Record (Word w))) :=
  let records := initRecord header site :: probeRecords start rs
  records.map some ++ List.replicate (4 * H - records.length) none

theorem siteRecordBlock_occupied (header : ℕ → Word w) (H site start : ℕ)
    (rs : List (Report w)) :
    (siteRecordBlock header H site start rs).filterMap id =
      initRecord header site :: probeRecords start rs := by
  simp [siteRecordBlock, List.filterMap_map]

theorem length_siteRecordBlock (header : ℕ → Word w) (H site start : ℕ) (rs : List (Report w))
    (hfit : 1 + RAMBuckets.probeCount Report.probes rs ≤ 4 * H) :
    (siteRecordBlock header H site start rs).length = 4 * H := by
  simp only [siteRecordBlock, List.length_append, List.length_map, List.length_cons,
    List.length_replicate, length_probeRecords]
  omega

/-- Encode consecutive sites starting at `site`, maintaining the actual
cumulative cost across the entire chain, including the sites after halt. -/
def recordBlocks (header : ℕ → Word w) (H : ℕ) :
    ℕ → ℕ → List (List (Report w)) → List (List (Option (Record (Word w))))
  | _, _, [] => []
  | site, start, front :: rest =>
    siteRecordBlock header H site start front ::
      recordBlocks header H (site + 1) (start + RAMBuckets.cost Report.probes front) rest

theorem length_recordBlocks (header : ℕ → Word w) (H site start : ℕ)
    (blocks : List (List (Report w))) :
    (recordBlocks header H site start blocks).length = blocks.length := by
  induction blocks generalizing site start with
  | nil => rfl
  | cons front rest ih => simp [recordBlocks, ih]

theorem recordBlocks_width (header : ℕ → Word w) (H site start : ℕ)
    (blocks : List (List (Report w)))
    (hfit : ∀ rs ∈ blocks, 1 + RAMBuckets.probeCount Report.probes rs ≤ 4 * H) :
    ∀ block ∈ recordBlocks header H site start blocks, block.length = 4 * H := by
  induction blocks generalizing site start with
  | nil => simp [recordBlocks]
  | cons front rest ih =>
    intro block hblock
    rcases List.mem_cons.mp hblock with rfl | hmem
    · exact length_siteRecordBlock header H site start front (hfit front (List.mem_cons_self ..))
    · exact ih _ _ (fun rs hrs => hfit rs (List.mem_cons_of_mem _ hrs)) block hmem

/-- The cost supplied to a site's encoder is the sum of the charges at
all preceding sites. Empty buckets contribute no charge. -/
theorem getElem_recordBlocks (header : ℕ → Word w) (H site start : ℕ)
    (blocks : List (List (Report w))) (i : ℕ) (hi : i < blocks.length) :
    (recordBlocks header H site start blocks)[i]'(by simpa [length_recordBlocks] using hi) =
      siteRecordBlock header H (site + i)
        (start + RAMBuckets.cost Report.probes (blocks.take i).flatten) blocks[i] := by
  induction blocks generalizing site start i with
  | nil => simp at hi
  | cons front rest ih =>
    cases i with
    | zero => simp [recordBlocks, RAMBuckets.cost]
    | succ i =>
      have hrest : i < rest.length := by simpa using hi
      simpa [recordBlocks, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (site + 1) (start + RAMBuckets.cost Report.probes front) i hrest

/-- Gather the initialization records in address order and the probes in time
order. Their interleaving within the physical array preserves their multiset. -/
theorem recordBlocks_perm (header : ℕ → Word w) (H site start : ℕ)
    (blocks : List (List (Report w))) :
    ((List.range' site blocks.length).map (initRecord header) ++
      probeRecords start blocks.flatten).Perm
      ((recordBlocks header H site start blocks).flatten.filterMap id) := by
  induction blocks generalizing site start with
  | nil => simp [recordBlocks, probeRecords]
  | cons front rest ih =>
    simp only [List.length_cons, List.range'_succ, List.map_cons, List.flatten_cons,
      probeRecords_append, List.cons_append, recordBlocks, List.filterMap_append,
      siteRecordBlock_occupied]
    apply List.Perm.cons
    exact (List.perm_append_comm_assoc _ _ _).trans ((ih _ _).append_left _)

/-- The input blocks for the global sort, obtained from the unique grouping
by starting costs. Even sites with no calls contribute their header record. -/
def canonicalRecordBlocks (header : ℕ → Word w) (S H : ℕ) (rs : List (Report w)) :
    List (List (Option (Record (Word w)))) :=
  recordBlocks header H 0 0 (RAMBuckets.partition Report.probes H 0 S 0 rs)

theorem length_canonicalRecordBlocks (header : ℕ → Word w) (S H : ℕ) (rs : List (Report w)) :
    (canonicalRecordBlocks header S H rs).length = S := by
  simp [canonicalRecordBlocks, length_recordBlocks]

/-- Read the physical row at site `v` directly from its canonical bucket,
using the total cost of the preceding buckets as its start. -/
theorem getElem_canonicalRecordBlocks (header : ℕ → Word w) (S H : ℕ)
    (rs : List (Report w)) (v : Fin S) :
    let buckets := RAMBuckets.partition Report.probes H 0 S 0 rs
    (canonicalRecordBlocks header S H rs)[v.val]'(by simp [length_canonicalRecordBlocks]) = siteRecordBlock header H v.val
      (RAMBuckets.cost Report.probes (buckets.take v.val).flatten)
      (buckets[v.val]'(by simp [buckets])) := by
  simpa [canonicalRecordBlocks] using
    getElem_recordBlocks header H 0 0 (RAMBuckets.partition Report.probes H 0 S 0 rs)
      v.val (by simp)

theorem canonicalRecordBlocks_width (header : ℕ → Word w) {S H : ℕ} {rs : List (Report w)}
    (hH : 0 < H) (hcap : RAMBuckets.cost Report.probes rs ≤ S * H)
    (hc : ∀ r ∈ rs, 1 + r.probes ≤ H) :
    ∀ block ∈ canonicalRecordBlocks header S H rs, block.length = 4 * H :=
  recordBlocks_width header H 0 0 _ fun ys hys =>
    (RAMBuckets.partition_block_bounds hH hcap hc ys hys).2

theorem length_flatten_canonicalRecordBlocks (header : ℕ → Word w) {S H : ℕ} {rs : List (Report w)}
    (hH : 0 < H) (hcap : RAMBuckets.cost Report.probes rs ≤ S * H)
    (hc : ∀ r ∈ rs, 1 + r.probes ≤ H) :
    (canonicalRecordBlocks header S H rs).flatten.length = S * (4 * H) := by
  let blocks := canonicalRecordBlocks header S H rs
  have hlen : blocks.map List.length = List.replicate blocks.length (4 * H) :=
    List.map_eq_replicate_iff.mpr (canonicalRecordBlocks_width header hH hcap hc)
  change blocks.flatten.length = S * (4 * H)
  rw [List.length_flatten, hlen, List.sum_replicate_nat, length_canonicalRecordBlocks]

theorem canonicalRecordBlocks_perm (header : ℕ → Word w) {S H : ℕ} {rs : List (Report w)}
    (hcap : RAMBuckets.cost Report.probes rs ≤ S * H) :
    (initialRecords S header ++ probeRecords 0 rs).Perm
      ((canonicalRecordBlocks header S H rs).flatten.filterMap id) := by
  have h := RAMBuckets.partition_spec (v := 0) (start := 0) (sites := S)
    (xs := rs) (fun _ => by simp) (by simpa using hcap)
  simpa only [canonicalRecordBlocks, RAMBuckets.length_partition, h.1, initialRecords,
    List.range_eq_range'] using
      recordBlocks_perm header H 0 0 (RAMBuckets.partition Report.probes H 0 S 0 rs)

end BurstRAM

end VPVNP
end Computability
end OAI
