import OAI.Computability.VPVNP.RAMBuckets
import OAI.Computability.VPVNP.RAMExecution
import OAI.Computability.VPVNP.RAMMemory

/-!
# Chronological probe records of a burst RAM execution

In Lemma 10.1 each external read or write emits a five-word record, carrying
its call's starting cost and its ordinal among the probes of that call.
Internal steps and binary choices produce no records. These timestamps are
strictly increasing, and the record-level memory checks recover the read
semantics of the original events.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMMemory

variable {w : ℕ}

/-- The number of external word probes made by the events. -/
def countProbes : List (Event w) → ℕ
  | [] => 0
  | .read _ _ :: es | .write _ _ :: es => 1 + countProbes es
  | _ :: es => countProbes es

/-- Number of external read and write events in this call report. -/
def Report.probes (r : Report w) : ℕ := countProbes r.events

/-- Probe ordinals start at zero and advance only at external reads and writes. -/
def eventRecords (start : ℕ) : ℕ → List (Event w) → List (Record (Word w))
  | _, [] => []
  | j, .read a v :: es => ⟨.read, a.val, v, start, j⟩ :: eventRecords start (j + 1) es
  | j, .write a v :: es => ⟨.write, a.val, v, start, j⟩ :: eventRecords start (j + 1) es
  | j, _ :: es => eventRecords start j es

/-- All non-initialization records emitted by the sequence of calls. -/
def probeRecords : ℕ → List (Report w) → List (Record (Word w))
  | _, [] => []
  | start, r :: rs => eventRecords start 0 r.events ++
    probeRecords (start + (1 + r.probes)) rs

theorem length_eventRecords (start j : ℕ) (es : List (Event w)) :
    (eventRecords start j es).length = countProbes es := by
  induction es generalizing j with
  | nil => rfl
  | cons e es ih => cases e <;> simp [eventRecords, countProbes, ih, Nat.add_comm]

theorem length_probeRecords (start : ℕ) (rs : List (Report w)) :
    (probeRecords start rs).length = RAMBuckets.probeCount Report.probes rs := by
  induction rs generalizing start with
  | nil => rfl
  | cons r rs ih =>
    simp [probeRecords, RAMBuckets.probeCount, length_eventRecords, ih, Report.probes]

theorem probeRecords_append (start : ℕ) (rs ts : List (Report w)) :
    probeRecords start (rs ++ ts) = probeRecords start rs ++
      probeRecords (start + RAMBuckets.cost Report.probes rs) ts := by
  induction rs generalizing start with
  | nil => simp [probeRecords, RAMBuckets.cost]
  | cons r rs ih => simp [probeRecords, RAMBuckets.cost, ih, List.append_assoc, Nat.add_assoc]

theorem mem_eventRecords {start j : ℕ} {es : List (Event w)} {r : Record (Word w)}
    (h : r ∈ eventRecords start j es) :
    r.kind ≠ .init ∧ r.startCost = start ∧ j ≤ r.ordinal := by
  induction es generalizing j with
  | nil => simp [eventRecords] at h
  | cons e es ih =>
    cases e with
    | tick | choice => exact ih h
    | read a v | write a v =>
      rcases List.mem_cons.mp h with rfl | ht
      · simp
      · obtain ⟨hk, hc, hj⟩ := ih ht
        exact ⟨hk, hc, by omega⟩

theorem mem_probeRecords {start : ℕ} {rs : List (Report w)} {r : Record (Word w)}
    (h : r ∈ probeRecords start rs) :
    r.kind ≠ .init ∧ start ≤ r.startCost := by
  induction rs generalizing start with
  | nil => simp [probeRecords] at h
  | cons s rs ih =>
    rcases List.mem_append.mp h with hs | ht
    · obtain ⟨hk, he, _⟩ := mem_eventRecords hs
      exact ⟨hk, he.ge⟩
    · obtain ⟨hk, hle⟩ := ih ht
      exact ⟨hk, by omega⟩

theorem chronological_eventRecords (start j : ℕ) (es : List (Event w)) :
    Chronological (eventRecords start j es) := by
  induction es generalizing j with
  | nil => exact List.Pairwise.nil
  | cons e es ih =>
    cases e with
    | tick | choice => exact ih j
    | read a v | write a v =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih (j + 1)⟩
      intro r hr
      obtain ⟨hk, hc, hj⟩ := mem_eventRecords hr
      simpa [Record.timestamp, Prod.Lex.toLex_lt_toLex, hk, hc] using (show j < r.ordinal from hj)

theorem chronological_probeRecords (start : ℕ) (rs : List (Report w)) :
    Chronological (probeRecords start rs) := by
  induction rs generalizing start with
  | nil => exact List.Pairwise.nil
  | cons r rs ih =>
    apply List.pairwise_append.mpr
    refine ⟨chronological_eventRecords .., ih _, ?_⟩
    intro a ha b hb
    obtain ⟨hka, hca, _⟩ := mem_eventRecords ha
    obtain ⟨hkb, hcb⟩ := mem_probeRecords hb
    have hlt : a.startCost < b.startCost := by omega
    simp [Record.timestamp, Prod.Lex.toLex_lt_toLex, hka, hkb, hlt]

private theorem eventRecords_reads_append (start j : ℕ) (es tail : List (Event w))
    (records : List (Record (Word w))) (m : Memory w)
    (h : ∀ m, ReadsCorrect m records ↔ Correct m tail) :
    ReadsCorrect m (eventRecords start j es ++ records) ↔ Correct m (es ++ tail) := by
  induction es generalizing m j with
  | nil => exact h m
  | cons e es ih =>
    cases e with
    | tick | choice => exact ih j m
    | read a v =>
      have hu : afterRecord m ⟨.read, a.val, v, start, j⟩ = m := by
        funext i
        simp [afterRecord]
      simp [eventRecords, ReadsCorrect, Correct, hu, ih]
    | write a v =>
      have hu : afterRecord m ⟨.write, a.val, v, start, j⟩ = writeMemory m a v := by
        funext i
        simp [afterRecord, writeMemory, Function.update_apply]
      simp [eventRecords, ReadsCorrect, Correct, update, hu, ih]

/-- Checking all read records chronologically is equivalent to checking the
actual events, starting from any prescribed external memory. -/
theorem readsCorrect_probeRecords (start : ℕ) (rs : List (Report w)) (m : Memory w) :
    ReadsCorrect m (probeRecords start rs) ↔ Correct m (rs.map Report.events).flatten := by
  induction rs generalizing m start with
  | nil => rfl
  | cons r rs ih => exact eventRecords_reads_append _ _ _ _ _ _ (ih _)

/-- The sorted-record check in Lemma 10.1 tests precisely the read answers of
the original call reports, including the first read at an initialized address. -/
theorem padded_read_check {S : ℕ} {header : ℕ → Word w} {rs : List (Report w)}
    {raw sorted : List (Option (Record (Word w)))}
    (hrecords : (initialRecords S header ++ probeRecords 0 rs).Perm (raw.filterMap id))
    (hperm : raw.Perm sorted) (hsorted : sorted.Pairwise fun x y => paddedKey x ≤ paddedKey y) :
    PredecessorCheck none (sorted.filterMap id) ↔
      Correct (initialMemory S header) (rs.map Report.events).flatten :=
  (padded_predecessorCheck_iff hrecords hperm hsorted (chronological_probeRecords ..)
    fun _ hr => (mem_probeRecords hr).1).trans (readsCorrect_probeRecords ..)

end BurstRAM

end VPVNP
end Computability
end OAI
