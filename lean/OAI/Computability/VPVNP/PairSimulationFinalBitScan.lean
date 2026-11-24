import OAI.Computability.VPVNP.PairSimulationTerminalSplice
import OAI.Computability.VPVNP.PairSimulationFinalBitWorker

/-!
# Native histories of the terminal shared-bit worker

The terminal header gives the total number of bits and their base address.
The worker consumes singleton choices in descending physical order and then
consumes one empty closing call. Replaying its reports builds the same memory
image as the shared-wire reports used by the contraction formula.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.FinalBits.Worker

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- The two header cells stay outside the address range written by the worker. -/
structure Layout (pub : Fin 11 → Word w) (m : Memory w) (lo count : ℕ) : Prop where
  base_eq : base pub m = (lo : Word w)
  total_eq : total pub m = (count : Word w)
  fits : lo + count < 2 ^ w
  base_disjoint : ∀ j < count, (header pub + 13).val ≠ lo + j
  total_disjoint : ∀ j < count, (header pub + 12).val ≠ lo + j

private theorem header_offset (pub : Fin 11 → Word w) (k : ℕ) (hk : k < 32)
    (room : (header pub).val + 32 ≤ 2 ^ w) :
    (header pub + (k : Word w)).val = (header pub).val + k := by
  rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : k < 2 ^ w),
    Nat.mod_eq_of_lt (by omega)]

/-- The physical wire interval ends below the terminal header. -/
theorem Layout.ofBelow {pub : Fin 11 → Word w} {m : Memory w} {lo count : ℕ}
    (hb : base pub m = (lo : Word w)) (ht : total pub m = (count : Word w))
    (below : lo + count ≤ (header pub).val) (room : (header pub).val + 32 ≤ 2 ^ w) :
    Layout pub m lo count := by
  refine ⟨hb, ht, by omega, ?_, ?_⟩
  · intro j hj
    rw [show (header pub + 13).val = _ from header_offset pub 13 (by decide) room]
    omega
  · intro j hj
    rw [show (header pub + 12).val = _ from header_offset pub 12 (by decide) room]
    omega

/-- The reports contain the actual header reads, choices, writes, returned
ordinals and the accepting report of the last call. -/
def reports (pub : Fin 11 → Word w) : (i : ℕ) → (m : Memory w) →
    {n : ℕ} → (Fin n → Bool) → List (Report w)
  | _, m, 0, _ => [closeReport pub m]
  | i, m, n + 1, f =>
    let r := activeReport pub (i : Word w) m (f (Fin.last n))
    r :: reports pub (i + 1) (after m r.events) (Fin.init f)

private theorem active_at {pub : Fin 11 → Word w} {m : Memory w} {lo count i n : ℕ}
    (h : Layout pub m lo count) (hcount : i + (n + 1) = count) :
    (i : Word w) < total pub m ∧ address pub m (i : Word w) = cursor w lo n := by
  have ht := h.fits
  constructor
  · rw [h.total_eq]
    change i % (2 ^ w) < count % (2 ^ w)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [address, h.base_eq, h.total_eq, ← hcount]
    simp only [cursor, Nat.cast_add, Nat.cast_one]
    abel

private theorem next_layout {pub : Fin 11 → Word w} {m : Memory w} {lo count i n : ℕ}
    (h : Layout pub m lo count) (hcount : i + (n + 1) = count) (b : Bool) :
    Layout pub (after m (activeReport pub (i : Word w) m b).events) lo count := by
  have hj : n < count := by omega
  have hv : (cursor w lo n).val = lo + n :=
    Nat.mod_eq_of_lt ((Nat.add_lt_add_left hj lo).trans h.fits)
  rw [active_image, (active_at h hcount).2]
  refine ⟨?_, ?_, h.fits, h.base_disjoint, h.total_disjoint⟩
  · simpa only [base, writeMemory, hv, ite_eq_right (h.base_disjoint n hj)] using h.base_eq
  · simpa only [total, writeMemory, hv, ite_eq_right (h.total_disjoint n hj)] using h.total_eq

private theorem run_from {pub : Fin 11 → Word w} {lo count : ℕ} (extra n i : ℕ)
    (m : Memory w) (h : Layout pub m lo count) (hcount : i + n = count) (f : Fin n → Bool) :
    runSegment (table.instantiate w pub).program (extra + 24) (some (i : Word w)) m
      (calls f ++ [[]]) = some (reports pub i m f) := by
  induction n generalizing i m with
  | zero =>
    have hi : (i : Word w) = total pub m := by simpa [← hcount] using h.total_eq.symm
    change runSegment _ _ (some (i : Word w)) m [[]] = _
    rw [runSegment, close pub _ m hi]
    rfl
  | succ n ih =>
    let b := f (Fin.last n)
    let m' := after m (activeReport pub (i : Word w) m b).events
    have tailRun := ih (i + 1) m' (next_layout h hcount b) (by omega) (Fin.init f)
    rw [calls_succ, List.cons_append, runSegment, active pub _ m (active_at h hcount).1]
    simp only [active_result, ← Nat.cast_add_one]
    change (runSegment _ _ (some ((i + 1 : ℕ) : Word w)) m' _).map _ = _
    rw [tailRun]
    rfl

/-- Full native execution from the zero ordinal, including the closing call. -/
theorem run_scan (pub : Fin 11 → Word w) (m : Memory w) {lo count : ℕ}
    (h : Layout pub m lo count) (f : Fin count → Bool) (extra : ℕ) :
    runSegment (table.instantiate w pub).program (extra + 24) (some 0) m
      (calls f ++ [[]]) = some (reports pub 0 m f) :=
  run_from extra count 0 m h (Nat.zero_add count) f

private theorem image_from {pub : Fin 11 → Word w} {lo count : ℕ} (n i : ℕ)
    (m : Memory w) (h : Layout pub m lo count) (hcount : i + n = count) (f : Fin n → Bool) :
    after m (eventLog (reports pub i m f)) = after m (eventLog (FinalBits.reports w lo f)) := by
  induction n generalizing i m with
  | zero => exact close_image pub m
  | succ n ih =>
    let b := f (Fin.last n)
    let m' := after m (activeReport pub (i : Word w) m b).events
    have tailRun := ih (i + 1) m' (next_layout h hcount b) (by omega) (Fin.init f)
    rw [reports, FinalBits.reports_succ]
    simp only [eventLog, List.flatMap_cons, after, List.foldl_append]
    change after m' (eventLog (reports pub (i + 1) m' (Fin.init f))) =
      after (after m (bitReport (cursor w lo n) b).events) (eventLog (FinalBits.reports w lo (Fin.init f)))
    rw [tailRun]
    have mem : m' = after m (bitReport (cursor w lo n) b).events := by
      rw [bitReport_memory, ← (active_at h hcount).2]
      exact active_image pub _ m b
    rw [mem]

/-- Native reports replay to the original reverse-order wire image. -/
theorem image (pub : Fin 11 → Word w) (m : Memory w) {lo count : ℕ}
    (h : Layout pub m lo count) (f : Fin count → Bool) :
    after m (eventLog (reports pub 0 m f)) = after m (eventLog (FinalBits.reports w lo f)) :=
  image_from count 0 m h (Nat.zero_add count) f

theorem readback (pub : Fin 11 → Word w) (m : Memory w) {lo count : ℕ}
    (h : Layout pub m lo count) (f : Fin count → Bool) (j : Fin count) :
    after m (eventLog (reports pub 0 m f)) (lo + j) = encodeBit w (f j) := by
  rw [image pub m h f]
  exact FinalBits.readback lo h.fits f m j

theorem outside (pub : Fin 11 → Word w) (m : Memory w) {lo count : ℕ}
    (h : Layout pub m lo count) (f : Fin count → Bool) (a : ℕ) (ha : a < lo ∨ lo + count ≤ a) :
    after m (eventLog (reports pub 0 m f)) a = m a := by
  rw [image pub m h f]
  exact FinalBits.outside lo h.fits f m a ha

theorem scan_cost (pub : Fin 11 → Word w) (n i : ℕ) (m : Memory w) (f : Fin n → Bool) :
    (reports pub i m f).length = n + 1 ∧
      RAMBuckets.cost Report.probes (reports pub i m f) = 4 * n + 2 ∧
      ∀ r ∈ reports pub i m f, r.probes ≤ 3 ∧ r.events.length ≤ 23 := by
  induction n generalizing i m with
  | zero =>
    simp only [reports, List.length_singleton, RAMBuckets.cost, (close_cost pub m).1,
      List.mem_singleton, forall_eq, (close_cost pub m).2]
    decide
  | succ n ih =>
    let b := f (Fin.last n)
    let r := activeReport pub (i : Word w) m b
    obtain ⟨hlen, hcost, hlocal⟩ := ih (i + 1) (after m r.events) (Fin.init f)
    have hr := active_cost pub (i : Word w) m b
    let rest := reports pub (i + 1) (after m r.events) (Fin.init f)
    change rest.length = _ at hlen
    change RAMBuckets.cost Report.probes rest = _ at hcost
    change (r :: rest).length = _ ∧ RAMBuckets.cost Report.probes (r :: rest) = _ ∧ ∀ s ∈ r :: rest, _
    change r.probes = 3 ∧ r.events.length = 23 at hr
    simp only [List.length_cons, hlen, RAMBuckets.cost, hr.1, hcost, List.mem_cons, forall_eq_or_imp]
    exact ⟨trivial, by omega, ⟨hr.1.le, hr.2.le⟩, hlocal⟩

private theorem complete_from {pub : Fin 11 → Word w} {lo count : ℕ} (extra n i : ℕ)
    (m : Memory w) (h : Layout pub m lo count) (hcount : i + n = count)
    (bs : List (List Bool)) (rs : List (Report w))
    (run : runSegment (table.instantiate w pub).program (extra + 24) (some (i : Word w)) m bs = some rs)
    (halt : endState (some (i : Word w)) rs = none) :
    ∃ f : Fin n → Bool, bs = calls f ++ [[]] ∧ rs = reports pub i m f := by
  induction n generalizing i m bs rs with
  | zero =>
    have hi : (i : Word w) = total pub m := by simpa [← hcount] using h.total_eq.symm
    cases bs with
    | nil =>
      obtain rfl : rs = [] := (Option.some.inj run).symm
      contradiction
    | cons head tail =>
      rw [runSegment, close pub _ m hi] at run
      cases head with
      | cons => contradiction
      | nil =>
        cases tail with
        | cons => contradiction
        | nil =>
          exact ⟨Fin.elim0, rfl, (Option.some.inj run).symm⟩
  | succ n ih =>
    cases bs with
    | nil =>
      obtain rfl : rs = [] := (Option.some.inj run).symm
      contradiction
    | cons head tail =>
      rw [runSegment, active pub _ m (active_at h hcount).1] at run
      cases head with
      | nil => contradiction
      | cons b rest =>
        cases rest with
        | cons => contradiction
        | nil =>
          obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp run
          let r := activeReport pub (i : Word w) m b
          have hs : r.result = some ((i + 1 : ℕ) : Word w) := by simp [r]
          change runSegment _ _ r.result (after m r.events) tail = some ts at hts
          change endState r.result ts = none at halt
          rw [hs] at hts halt
          obtain ⟨f, rfl, rfl⟩ := ih (i + 1) (after m r.events) (next_layout h hcount b)
            (by omega) tail ts hts halt
          refine ⟨Fin.snoc f b, ?_, ?_⟩
          · simp [calls_succ]
          · simp [reports, r]

theorem reports_halt (pub : Fin 11 → Word w) (n i : ℕ) (m : Memory w) (f : Fin n → Bool)
    (start : Option (Word w)) : endState start (reports pub i m f) = none := by
  induction n generalizing i m start with
  | zero => rfl
  | succ n ih => exact ih _ _ _ _

/-- Acceptance itself forces every data choice, the number of calls and the
single empty closing call. The reports retain the full native probe history. -/
theorem accepted_iff (pub : Fin 11 → Word w) (m : Memory w) {lo count : ℕ}
    (h : Layout pub m lo count) (extra : ℕ) (bs : List (List Bool)) (rs : List (Report w)) :
    (runSegment (table.instantiate w pub).program (extra + 24) (some 0) m bs = some rs ∧
      endState (some 0) rs = none) ↔
      ∃ f : Fin count → Bool, bs = calls f ++ [[]] ∧ rs = reports pub 0 m f := by
  constructor
  · rintro ⟨run, halt⟩
    exact complete_from extra count 0 m h (Nat.zero_add count) bs rs run halt
  · rintro ⟨f, rfl, rfl⟩
    exact ⟨run_scan pub m h f extra, reports_halt pub _ 0 m f _⟩

/-- Shared-bit assignments enumerate exactly the accepted paths. The cap
predicate may include clock and external-probe bounds on the actual reports. -/
noncomputable def acceptedEquiv (pub : Fin 11 → Word w) (m : Memory w) {lo count : ℕ}
    (h : Layout pub m lo count) (extra : ℕ) (caps : List (Report w) → Prop)
    (bound : ∀ f : Fin count → Bool, caps (reports pub 0 m f)) :
    (Fin count → Bool) ≃ ActualPaths (table.instantiate w pub).program (extra + 24) 0 m caps := by
  let path (f : Fin count → Bool) :
      ActualPaths (table.instantiate w pub).program (extra + 24) 0 m caps :=
    ⟨calls f ++ [[]], reports pub 0 m f, run_scan pub m h f extra, reports_halt pub _ 0 m f _, bound f⟩
  apply Equiv.ofBijective path
  constructor
  · intro f g he
    exact calls_injective (List.append_cancel_right (congrArg Subtype.val he))
  · rintro ⟨bs, rs, run, halt, _⟩
    obtain ⟨f, hf, _⟩ := (accepted_iff pub m h extra bs rs).mp ⟨run, halt⟩
    exact ⟨f, Subtype.ext hf.symm⟩

open CompressorRecords.SourceTransport
open private testEvents from OAI.Computability.VPVNP.PairSimulationFinalBitWorker

private def away (pub : Fin 11 → Word w) (x : ℕ) : Prop :=
  x ≠ (header pub).val ∧ x ≠ (header pub + 31).val

private theorem field_away (pub : Fin 11 → Word w) (room : (header pub).val + 32 ≤ 2 ^ w)
    (k : ℕ) (hk : 0 < k) (hk' : k < 31) : away pub (header pub + (k : Word w)).val := by
  rw [away, header_offset pub k (by omega) room,
    show (header pub + 31).val = _ from header_offset pub 31 (by decide) room]
  omega

private theorem active_frame {pub : Fin 11 → Word w} {m : Memory w} {i : Word w} (b : Bool)
    (room : (header pub).val + 32 ≤ 2 ^ w) (dest : away pub (address pub m i).val) :
    Reads (away pub) (activeReport pub i m b).events ∧ Writes (away pub) (activeReport pub i m b).events := by
  constructor <;> intro a v mem
  · simp only [activeReport, testEvents, List.mem_append, List.mem_replicate, List.mem_cons,
      List.not_mem_nil, Event.read.injEq, reduceCtorEq, and_false, false_or, or_false] at mem
    rcases mem with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact field_away pub room 12 (by decide) (by decide)
    · exact field_away pub room 13 (by decide) (by decide)
  · simp only [activeReport, testEvents, List.mem_append, List.mem_replicate, List.mem_cons,
      List.not_mem_nil, Event.write.injEq, reduceCtorEq, and_false, false_or, or_false] at mem
    obtain ⟨rfl, _⟩ := mem
    exact dest

private theorem close_frame (pub : Fin 11 → Word w) (m : Memory w)
    (room : (header pub).val + 32 ≤ 2 ^ w) :
    Reads (away pub) (closeReport pub m).events ∧ Writes (away pub) (closeReport pub m).events := by
  constructor <;> intro a v mem
  · simp only [closeReport, testEvents, List.mem_append, List.mem_replicate, List.mem_cons,
      List.not_mem_nil, Event.read.injEq, reduceCtorEq, and_false, false_or, or_false] at mem
    obtain ⟨rfl, _⟩ := mem
    exact field_away pub room 12 (by decide) (by decide)
  · simp only [closeReport, testEvents, List.mem_append, List.mem_replicate, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, and_false, false_or] at mem

private theorem frame_from {pub : Fin 11 → Word w} {lo count : ℕ} (n i : ℕ)
    (m : Memory w) (h : Layout pub m lo count) (hcount : i + n = count) (f : Fin n → Bool)
    (room : (header pub).val + 32 ≤ 2 ^ w) (below : lo + count ≤ (header pub).val) :
    ∀ r ∈ reports pub i m f, Reads (away pub) r.events ∧ Writes (away pub) r.events := by
  induction n generalizing i m with
  | zero =>
    simpa only [reports, List.mem_singleton, forall_eq] using close_frame pub m room
  | succ n ih =>
    intro r hr
    rw [reports, List.mem_cons] at hr
    rcases hr with rfl | hr
    · apply active_frame _ room
      rw [(active_at h hcount).2, away,
        show (header pub + 31).val = _ from header_offset pub 31 (by decide) room]
      have fit := h.fits
      change (lo + n) % (2 ^ w) ≠ _ ∧ (lo + n) % (2 ^ w) ≠ _
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · exact ih (i + 1) _ (next_layout h hcount _) (by omega) (Fin.init f) r hr

/-- All probes avoid the controller cells which hold the phase and the worker's
persistent state between calls. -/
theorem controller_frame (pub : Fin 11 → Word w) (m : Memory w) {lo count : ℕ}
    (h : Layout pub m lo count) (f : Fin count → Bool)
    (room : (header pub).val + 32 ≤ 2 ^ w) (below : lo + count ≤ (header pub).val) :
    let data := fun x => x ≠ (TerminalLink.header pub).val ∧ x ≠ (TerminalLink.header pub + 31).val
    Reads data (eventLog (reports pub 0 m f)) ∧ Writes data (eventLog (reports pub 0 m f)) := by
  have frames := frame_from count 0 m h (Nat.zero_add count) f room below
  constructor <;> intro a v mem
  · obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp mem
    exact (frames r hr).1 a v he
  · obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp mem
    exact (frames r hr).2 a v he

private theorem linked_cost (addr : Word w) (rs : List (Report w)) (state : Word w) :
    RAMBuckets.cost Report.probes (TerminalLink.stageReports addr (.resume TerminalLink.Stage.sharedBits state) rs) =
      RAMBuckets.cost Report.probes rs + 4 * rs.length := by
  induction rs generalizing state with
  | nil => rfl
  | cons r rs ih =>
    let e := TerminalLink.Entry.resume TerminalLink.Stage.sharedBits state
    have next : (e.follow r).isSome := by
      cases hr : r.result <;> simp only [e, TerminalLink.Entry.follow, TerminalLink.target, hr] <;> rfl
    rw [TerminalLink.stageReports, RAMBuckets.cost, TerminalLink.report_probes]
    change 1 + (r.probes + 2 + (if (e.follow r).isSome then 2 else 0)) + _ = _
    rw [next]
    simp only [↓reduceIte, RAMBuckets.cost, List.length_cons, TerminalLink.Entry.stage, ih]
    omega

/-- Each linked call costs four additional probes, including the handoff from
the accepting worker call to the vertex stage. -/
theorem stage_cost (pub : Fin 11 → Word w) (m : Memory w) {count : ℕ} (f : Fin count → Bool) :
    RAMBuckets.cost Report.probes (TerminalLink.stageReports (header pub)
      (.resume TerminalLink.Stage.sharedBits 0) (reports pub 0 m f)) = 8 * count + 6 := by
  obtain ⟨len, cost, _⟩ := scan_cost pub count 0 m f
  rw [linked_cost, cost, len]
  omega

/-- The shared-bit stage of the linked terminal program. Its physical reports
include the control reads and writes for each returned ordinal and the
handoff to the vertex worker after the closing call. -/
theorem stageRun (workers : TerminalLink.Stage → LiveProgram.PairTable)
    (bank : workers TerminalLink.Stage.sharedBits = ⟨28, 5, table⟩)
    (pub : Fin 11 → Word w) (src phy : Memory w) {lo count : ℕ}
    (h : Layout pub src lo count) (f : Fin count → Bool) (cap : ℕ)
    (clock : 54 ≤ cap) (room : (header pub).val + 32 ≤ 2 ^ w)
    (below : lo + count ≤ (header pub).val)
    (valid : (TerminalLink.Entry.resume TerminalLink.Stage.sharedBits (0 : Word w)).Valid (header pub) phy)
    (agree : Agree (TerminalLink.workerCell (header pub)) src phy) :
    TerminalLink.StageRun workers pub cap (.resume TerminalLink.Stage.sharedBits 0) src phy
      (calls f ++ [[]]) (reports pub 0 src f) := by
  apply TerminalLink.closed_stage_run workers pub 24 cap _ src phy _ _ (by omega) clock valid agree
    (controller_frame pub src h f room below).1
  · change runSegment ((workers TerminalLink.Stage.sharedBits).table.instantiate w pub).program 24
      (some 0) src _ = _
    rw [bank]
    exact run_scan pub src h f 0
  · exact reports_halt pub count 0 src f _

end PairSimulation.FinalBits.Worker

end VPVNP
end Computability
end OAI
