import OAI.Computability.VPVNP.PairTraversalControllerSelectedRun
import OAI.Computability.VPVNP.PairTraversalControllerTerminal
import OAI.Computability.VPVNP.PairTerminalQuietFrame
import OAI.Computability.VPVNP.PairTerminalFootprint

/-!
# Low-address preservation in each selected traversal report

The reference traversal preserves the low workspace after each tag, leaf and
fiber call. The controller inserts read-only setup and reset reports between
these calls. Its actual traversal therefore retains the low word at every
call boundary, including the final sentinel.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM CompressorRecords Compression LocalHistory TraversalRows DirectoryRun TraversalRoles
open TraversalControllerOrdinal TraversalControllerInputs
open scoped Fin.CommRing

variable {w : ℕ}

private def Holds (x : ℕ) (v : Word w) (r : Report w) : Prop :=
  ∀ mem : Memory w, mem x = v → after mem r.events x = v

private theorem holds_of_prefixes {x : ℕ} {m : Memory w} {rs : List (Report w)}
    (stable : ∀ i ≤ rs.length, after m (eventLog (rs.take i)) x = m x) :
    ∀ r ∈ rs, Holds x (m x) r := by
  intro r hr mem hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  let entry := after m (eventLog (rs.take i))
  have eq : mem x = entry x := hv.trans (stable i hi.le).symm
  have next := stable (i + 1) hi
  rw [List.take_succ_eq_append_getElem hi] at next
  simp only [eventLog, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, after, List.foldl_append] at next
  exact (ControllerMemory.after_at eq rs[i].events).trans next

private theorem replay_of_holds {x : ℕ} {v : Word w} {m : Memory w} {rs : List (Report w)}
    (start : m x = v) (each : ∀ r ∈ rs, Holds x v r) : ReplayFrame x m rs := by
  induction rs generalizing m with
  | nil => trivial
  | cons r rs ih =>
    have next := each r List.mem_cons_self m start
    exact ⟨next.trans start.symm, ih next (fun t ht => each t (List.mem_cons_of_mem r ht))⟩

open private Segment.one Segment.join located_count
  from OAI.Computability.VPVNP.PairTraversalControllerRun

/-- The controller lifts a word preserved at all reference-call boundaries
to a word preserved at every controller-call boundary. -/
theorem Segment.replay_of_reference (pub : Fin 11 → Word w) (L N fuel x : ℕ)
    {jobs : List (Pass w)} {m final : Memory w} {refs out : List (Report w)} {calls probes : ℕ}
    (completed : Segment (Native.machine pub).program fuel (some 0) none m final calls probes out)
    (ref : Reference jobs m refs) (levels : jobs.length = 2 * L) (positive : 0 < L)
    (fit : 2 * L * (N + 1) < 2 ^ w) (counts : ∀ j : Fin jobs.length, jobs[j].count ≤ N)
    (clock : ∀ j : Fin jobs.length, setupLen + 7 + jobs[j].clock ≤ fuel)
    (adminClock : setupLen + 8 ≤ fuel) (stable : AtPrefixes (RunInputs pub L N jobs) m refs)
    (rawFrame : ∀ i ≤ refs.length, after m (eventLog (refs.take i)) x = m x) :
    ReplayFrame x m out := by
  let P := (Native.machine pub).program
  let good := Holds x (m x)
  let ready := RunInputs pub L N jobs
  have phase (j : Fin jobs.length) : j.val < 2 * L := j.isLt.trans_eq levels
  have active (j : Fin jobs.length) :
      ActiveCalls P fuel N (0 + j.val) 257 jobs[j] ready good good := by
    rw [Nat.zero_add]
    intro i entry small ok source keeps
    obtain ⟨pre, admin, call⟩ := active_step pub entry L N j.val i.val ok.levels ok.initial
      positive (phase j) (i.isLt.le.trans (counts j)) fit _ (ok.located j) i.isLt small source
    have replay (mem : Memory w) : after mem (pre ++ small.events) = after mem small.events := by
      change (pre ++ small.events).foldl update mem = _
      rw [List.foldl_append, ← show after mem pre = pre.foldl update mem from rfl, admin.replay]
      rfl
    exact ⟨_, call fuel (clock j), rfl, replay entry,
      (countProbes_append pre small.events).trans (congrArg (· + small.probes) admin.probes),
      fun mem hv => (congrFun (replay mem) x).trans (keeps mem hv)⟩
  have reset (j : Fin jobs.length) : ClosingCall P fuel N (0 + j.val) 257 jobs[j] ready good := by
    rw [Nat.zero_add]
    intro entry ok
    obtain ⟨pre, admin, call⟩ := reset_step pub entry L N j.val jobs[j].count ok.levels ok.initial
      positive (phase j) (counts j) fit (located_count (ok.located j)).symm
    exact ⟨_, call fuel adminClock, rfl, admin.replay entry, admin.probes,
      fun mem hv => (congrFun (admin.replay mem) x).trans hv⟩
  obtain ⟨rs, stages, each⟩ := lift_passes ref N 0 257 ready stable good good
    (holds_of_prefixes rawFrame) active reset
  let last := after m (eventLog refs)
  have ok : ready last := by simpa only [List.take_length] using stable _ le_rfl
  obtain ⟨pre, admin, stop⟩ := stop_step pub last L N ok.levels ok.initial positive fit
  let sentinel : Report w := ⟨pre, none⟩
  have accept : Segment P fuel (some (pack N (2 * L) 0 : Word w)) none last (after last pre)
      1 sentinel.probes [sentinel] := Segment.one (stop fuel adminClock)
  rw [← levels] at accept
  rw [Nat.zero_add] at stages
  have complete := Segment.join stages accept
  rw [show (pack N 0 0 : Word w) = 0 by simp [pack]] at complete
  obtain ⟨_, rfl⟩ := complete.accepted_unique completed.run completed.endAt
  apply replay_of_holds (v := m x) rfl
  intro r hr
  rcases List.mem_append.mp hr with inside | endReport
  · exact each r inside
  · obtain rfl := List.mem_singleton.mp endReport
    exact fun mem hv => (congrFun (admin.replay mem) x).trans hv

open private tags_info selected_jobs_info
  from OAI.Computability.VPVNP.PairTraversalControllerSelectedRun

variable {k A : Type*} [Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) {n : ℕ} (T : ℕ)
variable (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices) (base : ℕ) (src : Memory w)
variable (ds : let vs := executeLevels B f hf T hT X z
  (i : Fin vs.length) → LevelDirectory vs[i] src base)
variable (pub : Fin 11 → Word w) (F H first pitch : ℕ)
variable (resident : Resident pub src H first pitch
    (words B.recordLimit (selectedLayers B f hf T hT X z) + F) B.recordLimit base
    ⟨leafLayer (siteOrder X), .cursor⟩ (levelFibers (executeLevels B f hf T hT X z) ds))
variable (heads : ∀ j ≤ (executeLevels B f hf T hT X z).length, first + j * pitch + 28 ≤ base)
variable (below : base + 2 * words B.recordLimit (selectedLayers B f hf T hT X z) + F ≤ H)
variable (ordinal : 2 * (selected B f hf T hT X z).length * (X.positions + 1) < 2 ^ w)

include resident heads below ordinal

/-- Each native controller report in the selected traversal preserves every
address below the row base, on its actual input memory. -/
theorem selected_low_replay {tags rows out : List (Report w)} {final : Memory w} {calls probes : ℕ}
    (ht : RolePasses (words B.recordLimit (selectedLayers B f hf T hT X z) + F) B.recordLimit
      base (selected B f hf T hT X z) src tags)
    (hr : DirectoryRun.Segments (selectedJobs B f hf T hT X z base src ds)
      (after src (eventLog tags)) rows)
    (completed : Segment (Native.machine pub).program (callFuel B.recordLimit) (some 0) none
      src final calls probes out) (x : ℕ) (hx : x < base) : ReplayFrame x src out := by
  let cap := B.recordLimit
  let tagLayers := selected B f hf T hT X z
  let layerList := selectedLayers B f hf T hT X z
  let bankSize := words cap layerList
  let offset := bankSize + F
  let directoryJobs := selectedJobs B f hf T hT X z base src ds
  change base + 2 * bankSize + F ≤ H at below
  change 2 * tagLayers.length * (X.positions + 1) < 2 ^ w at ordinal
  let jobs := tagJobs w offset cap base tagLayers ++ directoryJobs.map rowJob
  have tagSize : tagWords cap tagLayers = bankSize :=
    congrArg (words cap) (selected_layers B f hf T hT X z)
  have top : offset + base + tagWords cap tagLayers ≤ H := by
    rw [tagSize]
    dsimp only [offset]
    omega
  have headers := selected_reference_schedule B f hf T hT X z base src ds resident heads
    tags rows ht hr top
  have sched : Schedule pub src offset cap base tagLayers directoryJobs :=
    (headers 0 (Nat.zero_le _)).1
  have positive : 0 < tagLayers.length := Nat.succ_pos _
  have layerEq : tagLayers.map TaggedLayer.layer = layerList := selected_layers B f hf T hT X z
  have counts (j : Fin jobs.length) : jobs[j].count ≤ X.positions := by
    let layer : Fin tagLayers.length := ⟨j.val % tagLayers.length, Nat.mod_lt _ positive⟩
    rw [show jobs[j].count = _ from sched.pass_count j, (sched.lookup layer).1]
    apply selected_layer_count_le B f hf T hT X z
    change tagLayers[layer].layer ∈ layerList
    rw [← layerEq]
    exact List.mem_map_of_mem (List.getElem_mem layer.isLt)
  have clock (j : Fin jobs.length) : setupLen + 7 + jobs[j].clock ≤ callFuel cap := by
    apply Nat.add_le_add_left
    rcases List.mem_append.mp (List.getElem_mem (l := jobs) j.isLt) with h | h
    · exact ((tags_info (w := w) offset cap base tagLayers).2 _ h).trans_le (by omega)
    · obtain ⟨j, hj, e⟩ := List.mem_map.mp h
      exact e ▸ (selected_jobs_info B f hf T hT X z base src ds).2 j hj
  have typed : Reference jobs src (tags ++ rows) := Reference.of_passes ht hr
  have levels : jobs.length = 2 * tagLayers.length := by simp [jobs, sched.jobs_length, two_mul]
  apply Segment.replay_of_reference pub tagLayers.length X.positions (callFuel cap) x completed
    typed levels positive ordinal counts clock (by unfold callFuel; omega)
  · intro i hi
    obtain ⟨schedule, sites⟩ := headers i hi
    exact ⟨schedule.total, sites, schedule.located⟩
  · intro i hi
    exact selected_reference_frame B f hf T hT X z base src ds offset tags rows ht hr
      (top.trans_lt (by have := resident.headerFits; omega)) i hi x (Or.inl (by omega)) (Or.inl hx)

open TerminalLink

/-- Any completed physical traversal-row phase has the selected raw reports
with precisely their terminal dispatch and handoff writes. Every report
preserves the requested low word, on the memory supplied to that call. -/
theorem selected_linked_low_replay (workers : Stage → LiveProgram.PairTable) (outer : ℕ)
    (bank : workers Stage.traversalRows = ⟨Native.P, R, Native.table⟩)
    (room : callFuel B.recordLimit + 30 ≤ outer)
    {bs ls mem} (cand : Phase workers pub outer (.resume Stage.traversalRows 0) src bs ls mem)
    (x : ℕ) (hx : x < base) : ReplayFrame x src (reports (header pub) ls) := by
  have native :=
    selected_run_with_reads B f hf T hT X z base src ds pub F H first pitch resident heads
      below ordinal
  dsimp only at native
  obtain ⟨tags, rows, out, ht, hr, seg, _, _, _, _, _, _, reads, _⟩ := native
  have known := Phase.of_source_segment (workers := workers) (pub := pub)
    (e := Entry.resume Stage.traversalRows (0 : Word w)) room (fun _ _ => rfl) reads
    (by
      unfold source
      rw [show (Entry.resume Stage.traversalRows (0 : Word w)).stage = Stage.traversalRows from rfl,
        bank]
      exact seg.run) seg.endAt
  obtain ⟨_, hl, _⟩ := known.force_quiet (fun _ h => List.eq_of_mem_replicate h) cand
  rw [hl, reports_stageLogs]
  have head : (header pub).val = H := by
    change (terminalHead pub).val = H
    rw [resident.header, Fin.val_natCast, Nat.mod_eq_of_lt (by have := resident.headerFits; omega)]
  have away : workerCell (header pub) x := TerminalFootprint.below _
    (by rw [head]; have := resident.headerFits; omega) (by rw [head]; omega)
  exact replayFrame_stage (header pub) _ away out src src rfl
    (selected_low_replay B f hf T hT X z base src ds pub F H first pitch resident heads below
      ordinal ht hr seg x hx)

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
