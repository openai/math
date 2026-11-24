import OAI.Computability.VPVNP.PairTraversalControllerReference
import OAI.Computability.VPVNP.PairTraversalControllerStep
import OAI.Computability.VPVNP.LiveHeaderUnique

/-!
# Chronological execution of the traversal controller

The active site calls advance the packed persistent ordinal by one. The
extra call at the end of each layer resets the site digit and starts the
next phase-level. The final sentinel accepts. Every call receives the
post-memory of the preceding call, including across reset boundaries.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM TraversalControllerOrdinal TraversalControllerInputs
open scoped Fin.CommRing

variable {w : ℕ} {C : Type*}

/-- A native interval of deterministic controller calls, with its complete
post-memory, returned ordinal, and external probe total. -/
structure Segment (P : BurstRAM.Program w C) (fuel : ℕ) (first last : Option (Word w))
    (before final : Memory w) (calls probes : ℕ) (rs : List (Report w)) : Prop where
  run : runSegment P fuel first before (List.replicate calls []) = some rs
  endAt : endState first rs = last
  memory : after before (eventLog rs) = final
  length : rs.length = calls
  cost : countProbes (eventLog rs) = probes

private theorem replay_append (m : Memory w) (xs ys : List (Report w)) :
    after m (eventLog (xs ++ ys)) = after (after m (eventLog xs)) (eventLog ys) := by
  simp only [after, eventLog, List.flatMap_append, List.foldl_append]

private theorem cost_append (xs ys : List (Report w)) :
    countProbes (eventLog (xs ++ ys)) = countProbes (eventLog xs) + countProbes (eventLog ys) := by
  simp only [eventLog, List.flatMap_append, countProbes_append]

variable {P : BurstRAM.Program w C} {fuel : ℕ}

private theorem Segment.empty (s : Option (Word w)) (m : Memory w) :
    Segment P fuel s s m m 0 0 [] := ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem Segment.one {s : Word w} {m : Memory w} {r : Report w}
    (he : execute P fuel (P.start s) m [] = some r) :
    Segment P fuel (some s) r.result m (after m r.events) 1 r.probes [r] := by
  refine ⟨?_, rfl, ?_, rfl, ?_⟩
  · simp only [List.replicate_succ, List.replicate_zero, runSegment, he, Option.map_some]
  · simp only [eventLog, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · simp only [eventLog, List.flatMap_cons, List.flatMap_nil, List.append_nil, Report.probes]

private theorem Segment.join {s t u : Option (Word w)} {m n o : Memory w}
    {a b c d : ℕ} {rs ss : List (Report w)}
    (h : Segment P fuel s t m n a c rs) (k : Segment P fuel t u n o b d ss) :
    Segment P fuel s u m o (a+b) (c+d) (rs++ss) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.replicate_add, PrimedSchedule.runSegment_append, h.run]
    simp only [Option.bind_some, h.endAt, h.memory, k.run, Option.map_some]
  · rw [endState_append, h.endAt, k.endAt]
  · rw [replay_append, h.memory, k.memory]
  · rw [List.length_append, h.length, k.length]
  · rw [cost_append, h.cost, k.cost]

/-- Lift all active calls of a single layer, using the actual pre-memory
of each reference report. A zero-site layer has the empty active segment. -/
private theorem lift_sites (key : ℕ → Word w) (setup : ℕ) (m : Memory w) (refs : List (Report w))
    (good : Report w → Prop) (active : ∀ i : Fin refs.length,
      let entry := after m (eventLog (refs.take i.val))
      ∃ r, execute P fuel (P.start (key i.val)) entry [] = some r ∧
        r.result = some (key (i.val + 1)) ∧
        after entry r.events = after entry refs[i].events ∧ r.probes = setup + refs[i].probes ∧
        good r) :
    ∃ out, Segment P fuel (some (key 0)) (some (key refs.length))
      m (after m (eventLog refs)) refs.length (setup * refs.length + countProbes (eventLog refs))
      out ∧ ∀ r ∈ out, good r := by
  have partialRun (k : ℕ) (hk : k ≤ refs.length) :
      ∃ rs, Segment P fuel (some (key 0)) (some (key k)) m
        (after m (eventLog (refs.take k))) k (setup*k + countProbes (eventLog (refs.take k)))
          rs ∧ ∀ r ∈ rs, good r := by
    induction k with
    | zero => exact ⟨[], Segment.empty (some (key 0)) m, by simp⟩
    | succ k ih =>
      let i : Fin refs.length := ⟨k, hk⟩
      let entry := after m (eventLog (refs.take k))
      obtain ⟨rs, h, earlier⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨r, he, hs, hm, hp, latest⟩ := active i
      have one := Segment.one he
      rw [hs, hm, hp] at one
      have joined := h.join one
      refine ⟨rs ++ [r], ?_, fun a ha => (List.mem_append.mp ha).elim (earlier a)
        (fun h => List.mem_singleton.mp h ▸ latest)⟩
      rw [List.take_succ_eq_append_getElem hk, replay_append, cost_append, Nat.mul_succ]
      simpa only [i, Fin.getElem_fin, eventLog, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, Report.probes, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using joined
  simpa only [List.take_length] using partialRun refs.length le_rfl

/-- At every prefix, the resident schedule still supplies the same layer
counts and worker operands. -/
def AtPrefixes (ready : Memory w → Prop) (m : Memory w) (refs : List (Report w)) : Prop :=
  ∀ k ≤ refs.length, ready (after m (eventLog (refs.take k)))

private theorem AtPrefixes.split {ready : Memory w → Prop} {m : Memory w} {xs ys : List (Report w)}
    (h : AtPrefixes ready m (xs ++ ys)) :
    AtPrefixes ready m xs ∧ AtPrefixes ready (after m (eventLog xs)) ys := by
  constructor
  · intro i hi
    have hh := h i (by rw [List.length_append]; omega)
    rwa [List.take_append_of_le_length hi] at hh
  · intro j hj
    have hh := h (xs.length+j) (by simpa using hj)
    rwa [List.take_length_add_append, replay_append] at hh

/-- Successful native execution and report conditions for every active site of this traversal
pass from a ready memory. -/
def ActiveCalls (P : BurstRAM.Program w C) (fuel N phase setup : ℕ) (job : Pass w)
    (ready : Memory w → Prop) (sourceOK good : Report w → Prop) : Prop :=
  ∀ (i : Fin job.count) (m : Memory w) (small : Report w), ready m →
    job.At (i.val : Word w) m small → sourceOK small →
    ∃ r, execute P fuel (P.start (pack N phase i.val : Word w)) m [] = some r ∧
      r.result = some (pack N phase (i.val+1) : Word w) ∧
      after m r.events = after m small.events ∧ r.probes = setup + small.probes ∧ good r

/-- Native execution and report conditions for the closing call after the traversal pass has
processed its last site. -/
def ClosingCall (P : BurstRAM.Program w C) (fuel N phase setup : ℕ) (job : Pass w)
    (ready : Memory w → Prop) (good : Report w → Prop) : Prop :=
  ∀ (m : Memory w), ready m →
    ∃ r, execute P fuel (P.start (pack N phase job.count : Word w)) m [] = some r ∧
      r.result = some (pack N (phase+1) 0 : Word w) ∧ after m r.events = m ∧
      r.probes = setup ∧ good r

/-- Concatenate every physical pass with its own reset. The zero-size case
still executes that reset. Each wrapped site has the same post-memory as its
reference site, so the very next call reads the correct live data. -/
theorem lift_passes {jobs : List (Pass w)} {m : Memory w} {refs : List (Report w)}
    (ref : Reference jobs m refs) (N phase setup : ℕ) (ready : Memory w → Prop)
    (stable : AtPrefixes ready m refs) (sourceOK good : Report w → Prop)
    (sources : ∀ r ∈ refs, sourceOK r)
    (active : ∀ j : Fin jobs.length,
      ActiveCalls P fuel N (phase+j.val) setup jobs[j] ready sourceOK good)
    (close : ∀ j : Fin jobs.length, ClosingCall P fuel N (phase+j.val) setup jobs[j] ready good) :
    ∃ rs, Segment P fuel (some (pack N phase 0 : Word w))
      (some (pack N (phase + jobs.length) 0 : Word w)) m (after m (eventLog refs))
      (refs.length + jobs.length)
      (setup * (refs.length + jobs.length) + countProbes (eventLog refs)) rs ∧
      ∀ r ∈ rs, good r := by
  induction ref generalizing phase with
  | nil =>
    exact ⟨[], Segment.empty (some (pack N phase 0 : Word w)) _, by simp⟩
  | @cons job tail m localRefs restRefs run rest ih =>
    let mid := after m (eventLog localRefs)
    obtain ⟨here, later⟩ := stable.split
    have act : ActiveCalls P fuel N phase setup job ready sourceOK good := active 0
    have ending : ClosingCall P fuel N phase setup job ready good := close 0
    obtain ⟨ss, hs, goodSites⟩ := lift_sites (P := P) (fuel := fuel)
      (fun i => (pack N phase i : Word w))
      setup m localRefs good (fun i =>
        act ⟨i.val, i.isLt.trans_eq run.length⟩ _ _ (here _ i.isLt.le) (run.atSite i)
          (sources _ (List.mem_append_left restRefs (List.getElem_mem i.isLt))))
    have hm : ready mid := by simpa only [List.take_length, mid] using here _ le_rfl
    obtain ⟨stop, stopped, returned, same, probes, goodStop⟩ := ending mid hm
    have hstop := Segment.one stopped
    rw [returned, same, probes, ← run.length] at hstop
    have hpass := hs.join hstop
    have inc (j : Fin tail.length) : phase + j.succ.val = phase + 1 + j.val := by
      simp only [Fin.val_succ]; omega
    obtain ⟨rr, hr, goodTail⟩ := ih (phase+1) later
      (fun r h => sources r (List.mem_append_right localRefs h))
      (fun j => inc j ▸ active j.succ) (fun j => inc j ▸ close j.succ)
    have joined := hpass.join hr
    refine ⟨ss ++ [stop] ++ rr, ?_, ?_⟩
    rotate_left
    · intro r h
      rcases List.mem_append.mp h with before | last
      · exact (List.mem_append.mp before).elim (goodSites r)
          (fun h => List.mem_singleton.mp h ▸ goodStop)
      · exact goodTail r last
    rw [replay_append, cost_append, List.length_append, List.length_cons]
    rw [show phase + (tail.length + 1) = phase + 1 + tail.length by omega,
      show localRefs.length + restRefs.length + (tail.length + 1) =
        localRefs.length + 1 + (restRefs.length + tail.length) by omega]
    convert joined using 1
    ring

/-- A resident header supplies every actual worker lookup throughout the
prefixes of the selected reference run. -/
structure RunInputs (pub : Fin 11 → Word w) (L N : ℕ) (jobs : List (Pass w))
    (m : Memory w) : Prop where
  levels : (terminalField pub m 1).val = L
  initial : (siteCount pub m 0).val = N
  located : ∀ j : Fin jobs.length, jobs[j].Located pub m L j.val

private theorem located_count {pub : Fin 11 → Word w} {m : Memory w} {L p : ℕ} {job : Pass w}
    (h : job.Located pub m L p) : (siteCount pub m (p % L)).val = job.count := by
  cases job with
  | tag => exact h.2.2
  | leaf | fiber => exact h.2.2.2

/-- The single finite controller runs every reference burst in chronological
order. The final report accepts, the external memory is exactly the native
arena image, and the probe overhead counts every setup, reset and acceptance. -/
theorem run_reference (pub : Fin 11 → Word w) (L N fuel : ℕ)
    {jobs : List (Pass w)} {m : Memory w} {refs : List (Report w)}
    (ref : Reference jobs m refs) (levels : jobs.length = 2 * L) (positive : 0 < L)
    (fit : 2 * L * (N + 1) < 2 ^ w) (counts : ∀ j : Fin jobs.length, jobs[j].count ≤ N)
    (clock : ∀ j : Fin jobs.length, setupLen + 7 + jobs[j].clock ≤ fuel)
    (adminClock : setupLen + 8 ≤ fuel) (stable : AtPrefixes (RunInputs pub L N jobs) m refs) :
    let calls := refs.length + jobs.length + 1
    ∃ reports, Segment (Native.machine pub).program fuel (some 0) none m
      (after m (eventLog refs)) calls (257 * calls + countProbes (eventLog refs)) reports := by
  let P := (Native.machine pub).program
  let ready := RunInputs pub L N jobs
  have phase (j : Fin jobs.length) : j.val < 2 * L := j.isLt.trans_eq levels
  have active (j : Fin jobs.length) :
      ActiveCalls P fuel N (0 + j.val) 257 jobs[j] ready (fun _ => True) (fun _ => True) := by
    rw [Nat.zero_add]
    intro i entry small ok h _
    obtain ⟨pre, admin, call⟩ := active_step pub entry L N j.val i.val ok.levels ok.initial
      positive (phase j) (i.isLt.le.trans (counts j)) fit _ (ok.located j) i.isLt small h
    refine ⟨_, call fuel (clock j), rfl, ?_, ?_, trivial⟩
    · change after entry (pre ++ small.events) = _
      rw [show after entry (pre ++ small.events) = after (after entry pre) small.events from
        List.foldl_append, admin.replay]
    · exact (countProbes_append pre small.events).trans (congrArg (· + small.probes) admin.probes)
  have reset (j : Fin jobs.length) : ClosingCall P fuel N (0 + j.val) 257 jobs[j] ready
      (fun _ => True) := by
    rw [Nat.zero_add]
    intro entry ok
    obtain ⟨pre, admin, call⟩ := reset_step pub entry L N j.val jobs[j].count ok.levels ok.initial
      positive (phase j) (counts j) fit (located_count (ok.located j)).symm
    exact ⟨_, call fuel adminClock, rfl, admin.replay entry, admin.probes, trivial⟩
  obtain ⟨rs, stages, _⟩ := lift_passes ref N 0 257 ready stable (fun _ => True) (fun _ => True)
    (fun _ _ => trivial) active reset
  let final := after m (eventLog refs)
  have lastReady : ready final := by simpa only [List.take_length, final] using stable _ le_rfl
  obtain ⟨pre, admin, stop⟩ := stop_step pub final L N lastReady.levels lastReady.initial
    positive fit
  have sentinel := Segment.one (stop fuel adminClock)
  change Segment P fuel (some (pack N (2 * L) 0 : Word w)) none final
    (after final pre) 1 (countProbes pre) [⟨pre, none⟩] at sentinel
  rw [admin.replay, admin.probes, ← levels] at sentinel
  rw [Nat.zero_add] at stages
  have joined := stages.join sentinel
  refine ⟨rs ++ [⟨pre, none⟩], ?_⟩
  have hzero : (pack N 0 0 : Word w) = 0 := by simp [pack]
  rw [hzero] at joined
  convert joined using 1
  ring

/-- Every accepting tape for this deterministic controller gives the same
reports as the chronological run, including the reset and acceptance calls. -/
theorem Segment.accepted_unique {s : Option (Word w)} {m final : Memory w}
    {calls probes : ℕ} {rs : List (Report w)} (h : Segment P fuel s none m final calls probes rs)
    {bits : List (List Bool)} {out : List (Report w)}
    (actual : runSegment P fuel s m bits = some out) (done : endState s out = none) :
    bits = List.replicate calls [] ∧ out = rs :=
  accepted_empty_unique h.run h.endAt actual done

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
