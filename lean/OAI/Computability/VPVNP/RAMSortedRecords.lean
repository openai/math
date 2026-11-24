import OAI.Computability.VPVNP.RAMRecordBlocks
import OAI.Computability.VPVNP.RAMRecordIndex
import OAI.Computability.VPVNP.RAMRecordOrder
import OAI.Computability.VPVNP.RAMSortCorrect
import OAI.Computability.VPVNP.RAMSortPerm

/-!
# Checking the reads after the addressed Batcher sort

The canonical call buckets supply `2^d` contiguous blocks, each of width
`4 * 2^e`. The globally addressed sorting layers permute these very records.
Consequently the predecessor check on the final array recovers the original
read semantics from the headers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMMemory RAMSort

variable {w : ℕ}

/-- The padded records on the input wires. Outside the physical array the
wire function is extended by the empty slot. -/
def recordWires (header : ℕ → Word w) (d e : ℕ) (rs : List (Report w)) :
    ℕ → OrderedSlot (Word w) :=
  fun i => ⟨((canonicalRecordBlocks header (2^d) (2^e) rs).flatten[i]?).getD none⟩

private theorem record_block_width (e : ℕ) : 2 ^ (2 + e) = 4 * 2 ^ e := by
  rw [Nat.pow_add]

private theorem record_array_width (d e : ℕ) : 2 ^ ((2 + e) + d) = 2^d * (4 * 2^e) := by
  rw [Nat.pow_add, record_block_width, Nat.mul_comm]

/-- The finite input to the network is exactly the array produced by the
call buckets. Every comparison moves the full record. -/
theorem raw_recordWires (header : ℕ → Word w) {d e : ℕ} {rs : List (Report w)}
    (hcap : RAMBuckets.cost Report.probes rs ≤ 2^d * 2^e)
    (hc : ∀ r ∈ rs, 1 + r.probes ≤ 2^e) :
    List.ofFn (block ((2 + e) + d) 0 (recordWires header d e rs)) =
      (canonicalRecordBlocks header (2^d) (2^e) rs).flatten.map OrderedSlot.mk := by
  have hlen := length_flatten_canonicalRecordBlocks header (Nat.two_pow_pos e) hcap hc
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, hlen, record_array_width]
  intro i _ hi
  simp only [List.length_map] at hi
  simp only [List.getElem_ofFn, block, recordWires, Nat.zero_mul, Nat.zero_add,
    List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_map]

/-- Reading the aligned input block at site `v` uses precisely the records
from that site's canonical call bucket. -/
theorem block_recordWires (header : ℕ → Word w) {d e : ℕ} {rs : List (Report w)}
    (hcap : RAMBuckets.cost Report.probes rs ≤ 2^d * 2^e)
    (hc : ∀ r ∈ rs, 1 + r.probes ≤ 2^e) (v : Fin (2^d)) :
    List.ofFn (block (2 + e) v.val (recordWires header d e rs)) =
      ((canonicalRecordBlocks header (2^d) (2^e) rs)[v.val]'(by
        simp [length_canonicalRecordBlocks])).map OrderedSlot.mk := by
  let rows := canonicalRecordBlocks header (2^d) (2^e) rs
  have hw : ∀ row ∈ rows, row.length = 2 ^ (2 + e) := by
    rw [record_block_width]
    exact canonicalRecordBlocks_width header (Nat.two_pow_pos e) hcap hc
  have hv : v.val < rows.length := by simp [rows, length_canonicalRecordBlocks]
  have hrow := hw rows[v.val] (List.getElem_mem hv)
  apply List.ext_getElem
  · exact List.length_ofFn.trans ((List.length_map ..).trans hrow).symm
  intro j hj hj'
  have hjW : j < 2 ^ (2 + e) := by simpa only [List.length_ofFn] using hj
  have hjrow : j < rows[v.val].length := hrow.symm ▸ hjW
  simp only [List.getElem_ofFn, List.getElem_map, block, recordWires]
  change ⟨(rows.flatten[v.val * 2 ^ (2 + e) + j]?).getD none⟩ = OrderedSlot.mk rows[v.val][j]
  rw [getElem?_flatten_rect hw hv hjW, List.getElem?_eq_getElem hjrow]
  rfl

/-- The five-word slots after the last addressed layer of the network. -/
def sortedRecords (header : ℕ → Word w) (d e : ℕ) (rs : List (Report w)) :
    List (Option (Record (Word w))) :=
  let b := (2 + e) + d
  (List.ofFn (block b 0 (runPhases b (recordWires header d e rs)))).map OrderedSlot.record

/-- Concatenate the final blocks scanned by the physical site validators,
retaining every padding slot. -/
theorem flatten_sorted_record_blocks (header : ℕ → Word w) (d e : ℕ) (rs : List (Report w)) :
    let h := 2 + e
    let output := runPhases (h + d) (recordWires header d e rs)
    (List.ofFn fun v : Fin (2^d) =>
      (List.ofFn (block h v.val output)).map OrderedSlot.record).flatten =
      sortedRecords header d e rs := by
  let h := 2 + e
  let output := runPhases (h + d) (recordWires header d e rs)
  simpa only [sortedRecords, List.map_flatten, List.map_ofFn, Function.comp_def] using
    congrArg (List.map OrderedSlot.record) (flatten_ofFn_blocks h d output)

/-- The physical ascending output contains exactly the original padded records. -/
theorem sortedRecords_perm (header : ℕ → Word w) {d e : ℕ} {rs : List (Report w)}
    (hcap : RAMBuckets.cost Report.probes rs ≤ 2^d * 2^e)
    (hc : ∀ r ∈ rs, 1 + r.probes ≤ 2^e) :
    (canonicalRecordBlocks header (2^d) (2^e) rs).flatten.Perm (sortedRecords header d e rs) := by
  let b := (2 + e) + d
  let x := recordWires header d e rs
  have hp := ((sort_perm b true (block b 0 x)).symm).map OrderedSlot.record
  rw [show List.ofFn (block b 0 x) = _ from raw_recordWires header hcap hc] at hp
  have hid : OrderedSlot.record ∘ (@OrderedSlot.mk (Word w)) = id := rfl
  simpa only [sortedRecords, block_runPhases, Nat.zero_mod, decide_true, b, x, List.map_map,
    hid, List.map_id_fun, id_eq] using hp

/-- The physical output is in the paper's padded-key order. -/
theorem sortedRecords_sorted (header : ℕ → Word w) (d e : ℕ) (rs : List (Report w)) :
    (sortedRecords header d e rs).Pairwise fun x y => paddedKey x ≤ paddedKey y := by
  simp only [sortedRecords, block_runPhases, Nat.zero_mod, decide_true, List.pairwise_map,
    List.pairwise_ofFn]
  intro i j hij
  exact paddedKey_mono (sort_monotone _ _ hij.le)

/-- The local predecessor rule applied to the actual sorting-network output
accepts exactly the correct read guesses of the original RAM events. -/
theorem sortedRecords_read_check (header : ℕ → Word w) {d e : ℕ} {rs : List (Report w)}
    (hcap : RAMBuckets.cost Report.probes rs ≤ 2^d * 2^e)
    (hc : ∀ r ∈ rs, 1 + r.probes ≤ 2^e) :
    PaddedCheck none (sortedRecords header d e rs) ↔
      Correct (initialMemory (2^d) header) (rs.map Report.events).flatten :=
  (paddedCheck_iff_filter (sortedRecords_sorted ..) none).trans
    (padded_read_check (canonicalRecordBlocks_perm header hcap)
      (sortedRecords_perm header hcap hc) (sortedRecords_sorted ..))

end BurstRAM

end VPVNP
end Computability
end OAI
