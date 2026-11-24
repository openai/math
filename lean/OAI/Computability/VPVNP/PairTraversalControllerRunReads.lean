import OAI.Computability.VPVNP.PairTraversalControllerRun
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# Read footprint of a complete traversal-controller execution

At each active ordinal the wrapper reads only its operand bank and the
words read by the corresponding reference report. The resets and the
final acceptance read only their operand banks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM CompressorRecords TraversalControllerOrdinal TraversalControllerInputs
open scoped Fin.CommRing
open private Segment.one Segment.join located_count
  from OAI.Computability.VPVNP.PairTraversalControllerRun

variable {w : ℕ}

/-- Transfer the read footprint of the reference body and every live
register setup to the unique accepting native execution. -/
theorem Segment.reads (pub : Fin 11 → Word w) (L N fuel : ℕ) (data : ℕ → Prop)
    {jobs : List (Pass w)} {m : Memory w} {refs out : List (Report w)}
    {calls probes : ℕ} {final : Memory w}
    (completed : Segment (Native.machine pub).program fuel (some 0) none m final calls probes out)
    (ref : Reference jobs m refs) (levels : jobs.length = 2 * L) (positive : 0 < L)
    (fit : 2 * L * (N + 1) < 2 ^ w) (counts : ∀ j : Fin jobs.length, jobs[j].count ≤ N)
    (clock : ∀ j : Fin jobs.length, setupLen + 7 + jobs[j].clock ≤ fuel)
    (adminClock : setupLen + 8 ≤ fuel) (stable : AtPrefixes (RunInputs pub L N jobs) m refs)
    (refReads : SourceTransport.Reads data (eventLog refs))
    (setupReads : ∀ q ≤ refs.length, ∀ s regs, SourceTransport.Reads data
      (Native.prefixTrace pub s (after m (eventLog (refs.take q))) regs)) :
    SourceTransport.Reads data (eventLog out) := by
  let P := (Native.machine pub).program
  let good (r : Report w) := SourceTransport.Reads data r.events
  let ready (mem : Memory w) := RunInputs pub L N jobs mem ∧
    ∀ s regs, SourceTransport.Reads data (Native.prefixTrace pub s mem regs)
  have allSources (r : Report w) (hr : r ∈ refs) : good r :=
    fun a v ha => refReads a v (List.mem_flatMap.mpr ⟨r, hr, ha⟩)
  have allReady : AtPrefixes ready m refs := fun q hq => ⟨stable q hq, setupReads q hq⟩
  have phase (j : Fin jobs.length) : j.val < 2 * L := j.isLt.trans_eq levels
  have active (j : Fin jobs.length) :
      ActiveCalls P fuel N (0 + j.val) 257 jobs[j] ready good good := by
    rw [Nat.zero_add]
    intro i entry small ok source smallReads
    obtain ⟨pre, admin, ⟨regs, trace⟩, call⟩ := active_step_trace pub entry L N j.val i.val
      ok.1.levels ok.1.initial positive (phase j) (i.isLt.le.trans (counts j)) fit _
      (ok.1.located j) i.isLt small source
    refine ⟨_, call fuel (clock j), rfl, ?_, ?_, ?_⟩
    · change after entry (pre ++ small.events) = _
      rw [show after entry (pre ++ small.events) = after (after entry pre) small.events from
        List.foldl_append, admin.replay]
    · exact (countProbes_append pre small.events).trans (congrArg (· + small.probes) admin.probes)
    · intro a v h
      exact (List.mem_append.mp h).elim
        (fun h => ok.2 _ regs a v (trace ▸ h)) (smallReads a v)
  have reset (j : Fin jobs.length) : ClosingCall P fuel N (0 + j.val) 257 jobs[j] ready good := by
    rw [Nat.zero_add]
    intro entry ok
    obtain ⟨pre, admin, ⟨regs, trace⟩, call⟩ := reset_step_trace pub entry L N j.val jobs[j].count
      ok.1.levels ok.1.initial positive (phase j) (counts j) fit
      (located_count (ok.1.located j)).symm
    exact ⟨_, call fuel adminClock, rfl, admin.replay entry, admin.probes, trace ▸ ok.2 _ regs⟩
  obtain ⟨rs, stages, passed⟩ := lift_passes ref N 0 257 ready allReady good good allSources
    active reset
  let last := after m (eventLog refs)
  have ok : ready last := by simpa only [List.take_length, last] using allReady _ le_rfl
  obtain ⟨pre, admin, ⟨regs, trace⟩, stop⟩ := stop_step_trace pub last L N ok.1.levels ok.1.initial
    positive fit
  let sentinel : Report w := ⟨pre, none⟩
  have endReads : good sentinel := by
    change SourceTransport.Reads data pre
    rw [trace]
    exact ok.2 _ regs
  have accept : Segment P fuel (some (pack N (2 * L) 0 : Word w)) none last (after last pre)
      1 sentinel.probes [sentinel] := Segment.one (stop fuel adminClock)
  rw [← levels] at accept
  rw [Nat.zero_add] at stages
  have complete := Segment.join stages accept
  rw [show (pack N 0 0 : Word w) = 0 by simp [pack]] at complete
  obtain ⟨_, eqn⟩ := complete.accepted_unique completed.run completed.endAt
  rw [eqn]
  intro a v h
  obtain ⟨r, hr, hcell⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hr with earlier | final
  · exact passed r earlier a v hcell
  · obtain rfl := List.mem_singleton.mp final
    exact endReads a v hcell

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
