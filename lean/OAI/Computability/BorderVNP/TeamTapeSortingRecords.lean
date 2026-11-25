import OAI.Computability.BorderVNP.TeamRecords
import OAI.Computability.VPVNP.RAMBitTranscript

/-!
# Sorting physical read/write pairs for team probes

The named-stack memory pass checks the old word on reads. To check it on *every*
companion-paper probe, each probe is expanded into a read of its `before` field and a
write of its `after` field. They have consecutive ordinals at the same address and
logical time. Thus the existing fixed verifier checks exactly the four-word relation,
including overwrites and time-zero input initializations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeSorting

open VPVNP BurstRAM RAMMemory RAMSort RAMSerialization

variable {w h d : ℕ}

/-- Parse bounded emitted records on the initial wires. The optional value marks padding. -/
def wire (x : ℕ → Option (WordRecord w)) (i : ℕ) : OrderedSlot (Word w) :=
  ⟨(x i).map WordRecord.record⟩

/-- All active records in the finite physical input before sorting. -/
def occupied (b : ℕ) (x : ℕ → Option (WordRecord w)) : List (RAMMemory.Record (Word w)) :=
  (List.ofFn (block b 0 (wire x))).filterMap OrderedSlot.record

/-- A four-word probe is representable if its address, doubled address with a phase bit,
and logical tick fit the physical word. The before/after payloads already have this width. -/
def ProbeFits (r : TeamRecords.Record (Word w)) : Prop :=
  2 * r.address + 1 < 2^w ∧ r.tick < 2^w

/-- The physical pair to emit into the sorting buffer for a single bounded probe. -/
def wordPair (r : TeamRecords.Record (Word w)) (hr : ProbeFits r) : List (WordRecord w) :=
  [WordRecord.ofRecord (TeamRecords.inputRecord r)
      ⟨by have := hr.1; change r.address < 2^w; omega, hr.2,
        by have := hr.1; change 2 * r.address < 2^w; omega⟩,
    WordRecord.ofRecord (TeamRecords.outputRecord r)
      ⟨by have := hr.1; change r.address < 2^w; omega, hr.2, hr.1⟩]

/-- Reading the serialized pair produces precisely the two chronological memory records. -/
theorem wordPair_decode (r : TeamRecords.Record (Word w)) (hr : ProbeFits r) :
    (wordPair r hr).map WordRecord.record = TeamRecords.pair r := rfl

/-- One extra address bit suffices for the phase ordinal of both physical records. -/
theorem doubledAddress_fits {address : ℕ} (ha : address < 2^w) :
    2*address+1 < 2^(w+1) := by rw [pow_succ]; omega

private theorem sortedFlat (x : ℕ → Option (WordRecord w)) :
    RAMBoundary.flat (sortedBlock h d (wire x)) =
      (List.ofFn (sort (h+d) true (block (h+d) 0 (wire x)))).map OrderedSlot.record := by
  let y := runPhases (h+d) (wire x)
  have eq := flatten_ofFn_blocks h d (fun i => (y i).record)
  calc
    _ = List.ofFn (block (h+d) 0 (fun i => (y i).record)) := eq
    _ = (List.ofFn (block (h+d) 0 y)).map OrderedSlot.record := by rw [List.map_ofFn]; rfl
    _ = _ := by simp only [y, block_runPhases, Nat.zero_mod, decide_true]

/-- The old bitonic memory verifier on read/write pairs accepts precisely the unique
companion-paper path transcript. Local checks also force all sorting and boundary messages. -/
theorem pairedMemory_iff_transcript (x : ℕ → Option (WordRecord w)) (m : MemoryMessages h d w)
    {es : List (TeamRecords.Access (Word w))} {rs : List (TeamRecords.Record (Word w))}
    (he : TeamRecords.Matches es rs) (ht : TeamRecords.Timed es)
    (hp : (rs.flatMap TeamRecords.pair).Perm (occupied (h+d) x)) :
    (∀ v, MemoryAt m v (block h v.val (wire x))) ↔
      m = actualMemoryMessages h d (wire x) ∧ rs = TeamRecords.transcript (fun _ => 0) es := by
  let ys := List.ofFn (sort (h+d) true (block (h+d) 0 (wire x)))
  let zs := ys.map OrderedSlot.record
  have hz : zs.Pairwise fun a b => paddedKey a ≤ paddedKey b := by
    apply List.pairwise_map.mpr
    exact List.pairwise_ofFn.mpr fun _ _ hij => paddedKey_mono (sort_monotone _ _ hij.le)
  have hperm : (rs.flatMap TeamRecords.pair).Perm (zs.filterMap id) := by
    have hs := (sort_perm (h+d) true (block (h+d) 0 (wire x))).symm.filterMap OrderedSlot.record
    simpa only [zs, ys, List.filterMap_map, Function.id_comp] using hp.trans hs
  have hchron := TeamRecords.pair_chronological (TeamRecords.chronological_of_matches he ht)
  have hzread := predecessorCheck_iff_readsCorrect hperm hchron (addressSorted_of_padded_sort hperm hchron hz)
  rw [memoryAt_iff, sortedFlat]
  exact and_congr_right' <| (paddedCheck_iff_filter hz none).trans <| hzread.trans <|
    (TeamRecords.memoryCheck_pair rs _).trans (TeamRecords.memoryCheck_iff_transcript he _)

/-- All true exchange records fit the physical words because comparisons only move complete
input slots. This includes every last-slot boundary record. -/
theorem actualFits (x : ℕ → Option (WordRecord w)) :
    (actualMemoryMessages h d (wire x)).FitsWord := by
  let P (s : OrderedSlot (Word w)) := ∀ t ∈ s.record, RecordFitsWord t
  have hx : ∀ i, P (wire x i) := by
    intro i t ht
    change (x i).map WordRecord.record = some t at ht
    obtain ⟨z, _, rfl⟩ := Option.map_eq_some_iff.mp ht
    exact ⟨z.address.isLt, z.startCost.isLt, z.ordinal.isLt⟩
  exact ⟨fun l v i => actual_sortSends_preserves _ _ hx l v i,
    fun j => runPhases_preserves _ hx _⟩

end TeamTapeSorting

end BorderVNP
end Computability
end OAI
