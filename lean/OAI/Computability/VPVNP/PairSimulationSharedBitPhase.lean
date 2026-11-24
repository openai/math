import OAI.Computability.VPVNP.PairSimulationFinalBitScan
import OAI.Computability.VPVNP.PairSimulationTerminalBlocks
import OAI.Computability.VPVNP.PairSimulationTerminalProgram
import OAI.Computability.VPVNP.PairSimulationTerminalPhaseBuild

/-!
# The completed shared-bit phase of the terminal machine

The phase reads the base and size of the wire bank from its terminal header.
Every binary assignment determines one complete physical record, including
the closing call and the handoff to the vertex worker. The reverse direction
classifies the reads of an arbitrary successful worker call before
transporting its reports back to the ordinary shared-bit scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.SharedBitPhase

open BurstRAM PrivateRAM CompressorRecords TerminalLink
open SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} (F : DescriptorSpace.Shape) (limit : ℕ)
  (S : VertexImage.Part → VertexImage.Segment)
variable (pub : Fin 11 → Word w) (cap : ℕ)

open private testEvents from OAI.Computability.VPVNP.PairSimulationFinalBitWorker
open private field_away header_offset from OAI.Computability.VPVNP.PairSimulationFinalBitScan
open FinalBits.Worker (activeReport closeReport total)

/-- Every successful call, even on an arbitrary candidate tape and memory,
reads only header words 12 and 13. -/
private theorem call_reads (i : Word w) (m : Memory w) (b : List Bool) (r : Report w)
    {fuel : ℕ} (enough : 24 ≤ fuel) (room : (header pub).val + 32 ≤ 2 ^ w)
    (hc : execute (FinalBits.Worker.table.instantiate w pub).program fuel
      ((FinalBits.Worker.table.instantiate w pub).program.start i) m b = some r) :
    Reads (workerCell (header pub)) r.events := by
  rw [show fuel = (fuel - 24) + 24 by omega] at hc
  rcases lt_trichotomy i (total pub m) with hi | hi | hi
  · rw [FinalBits.Worker.active pub i m hi] at hc
    cases b with
    | nil => contradiction
    | cons b bs =>
      cases bs with
      | cons => contradiction
      | nil =>
        obtain rfl : r = activeReport pub i m b := (Option.some.inj hc).symm
        intro a v mem
        simp only [activeReport, testEvents, List.mem_append, List.mem_replicate, List.mem_cons,
          List.not_mem_nil, Event.read.injEq, reduceCtorEq, and_false, false_or, or_false] at mem
        rcases mem with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact field_away pub room 12 (by decide) (by decide)
        · exact field_away pub room 13 (by decide) (by decide)
  · rw [FinalBits.Worker.close pub i m hi] at hc
    split at hc <;> try contradiction
    obtain rfl : r = closeReport pub m := (Option.some.inj hc).symm
    intro a v mem
    simp only [closeReport, testEvents, List.mem_append, List.mem_replicate, List.mem_cons,
      List.not_mem_nil, Event.read.injEq, reduceCtorEq, and_false, false_or, or_false] at mem
    obtain ⟨rfl, _⟩ := mem
    exact field_away pub room 12 (by decide) (by decide)
  · rw [FinalBits.Worker.overrun pub i m hi] at hc
    contradiction

private theorem phase_reads {e phy bs ls final}
    (h : Phase (TerminalProgram.workers F limit S) pub cap e phy bs ls final)
    (stage : e.stage = Stage.sharedBits) (clock : 54 ≤ cap) (room : (header pub).val + 32 ≤ 2 ^ w) :
    Reads (workerCell (header pub)) (eventLog (ls.map Prod.snd)) := by
  have head {e : Entry w} {m b r} (stage : e.stage = Stage.sharedBits)
      (call : execute (source (TerminalProgram.workers F limit S) e.stage pub) (rawFuel pub cap e)
        ((source (TerminalProgram.workers F limit S) e.stage pub).start e.state) m b = some r) :
      Reads (workerCell (header pub)) r.events := by
    rw [stage] at call
    have pre := prefix_length_le (header pub) e
    apply call_reads pub e.state m b r (fuel := rawFuel pub cap e) (by unfold rawFuel; omega) room
    exact call
  induction h with
  | last hc _ _ => simpa only [List.map_cons, List.map_nil, eventLog, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] using head stage hc
  | more hc _ _ _ ih =>
    intro a v mem
    change Event.read a v ∈ _ ++ eventLog _ at mem
    rcases List.mem_append.mp mem with hh | ht
    · exact head stage hc a v hh
    · exact ih stage a v ht

/-- The physical phase record for an assignment to the entire wire bank. -/
def block (src phy : Memory w) {count : ℕ} (f : Fin count → Bool) : Block w :=
  let e := Entry.resume Stage.sharedBits (0 : Word w)
  let rs := FinalBits.Worker.reports pub 0 src f
  ⟨FinalBits.calls f ++ [[]], stageLogs e rs, after phy (eventLog (stageReports (header pub) e rs))⟩

variable (src phy : Memory w) {lo count : ℕ}
variable (layout : FinalBits.Worker.Layout pub src lo count) (clock : 54 ≤ cap)
  (room : (header pub).val + 32 ≤ 2 ^ w) (below : lo + count ≤ (header pub).val)
  (agree : Agree (workerCell (header pub)) src phy)

include layout clock room below agree

/-- All three components of the physical record are forced by its bit assignment. -/
theorem phase_iff (B : Block w) :
    Phase (TerminalProgram.workers F limit S) pub cap (.resume Stage.sharedBits 0)
      phy B.choices B.logs B.memory ↔ ∃ f : Fin count → Bool, B = block pub src phy f := by
  constructor
  · intro ph
    have ⟨run, halt, _⟩ := ph.source_segment _ _ _ src agree
      (phase_reads F limit S pub cap ph rfl clock room)
    change runSegment (FinalBits.Worker.table.instantiate w pub).program
      cap (some 0) src _ = _ at run
    rw [show cap = (cap - 24) + 24 by omega] at run
    obtain ⟨f, hb, hr⟩ :=
      (FinalBits.Worker.accepted_iff pub src layout (cap - 24) _ _).mp ⟨run, halt⟩
    have hl := stageLogs_eq ph
    rw [hr] at hl
    have hm := ph.final_memory
    rw [ph.reports_eq, hr] at hm
    exact ⟨f, by cases B; simp only [block, Block.mk.injEq]; exact ⟨hb, hl, hm.symm⟩⟩
  · rintro ⟨f, rfl⟩
    apply Phase.of_source_segment (f := 24) clock agree
      (FinalBits.Worker.controller_frame pub src layout f room below).1
    · exact FinalBits.Worker.run_scan pub src layout f 0
    · exact FinalBits.Worker.reports_halt pub count 0 src f _

/-- Binary wire assignments enumerate all completed records with their
individual private strings, raw tagged reports, and final physical memories. -/
noncomputable def equiv :
    (Fin count → Bool) ≃ CompletedPhase (TerminalProgram.workers F limit S) pub cap
      (.resume Stage.sharedBits 0) phy :=
  Equiv.ofBijective (fun f => ⟨block pub src phy f,
    (phase_iff F limit S pub cap src phy layout clock room below agree _).mpr ⟨f, rfl⟩⟩) <| by
    constructor
    · intro f g h
      exact FinalBits.calls_injective
        (List.append_cancel_right (congrArg (fun B => B.val.choices) h))
    · rintro ⟨B, ph⟩
      obtain ⟨f, rfl⟩ := (phase_iff F limit S pub cap src phy layout clock room below agree B).mp ph
      exact ⟨f, rfl⟩

variable (valid : (Entry.resume Stage.sharedBits (0 : Word w)).Valid (header pub) phy)

include F limit S valid

/-- Native execution realizes the completed block and initializes the vertex
worker's stage and ordinal in the two control cells. -/
theorem native (f : Fin count → Bool) :
    let B := block pub src phy f
    let e := Entry.resume Stage.sharedBits (0 : Word w)
    runSegment (program (TerminalProgram.workers F limit S) pub) cap (some e.marker)
      phy B.choices = some (reports (header pub) B.logs) ∧
    (Entry.resume Stage.vertices (0 : Word w)).Valid (header pub) B.memory := by
  have run := FinalBits.Worker.stageRun (TerminalProgram.workers F limit S) rfl pub src phy
    layout f cap clock room below valid agree
  refine ⟨?_, run.valid _ rfl⟩
  dsimp only [block]
  rw [reports_stageLogs]
  exact run.run

/-- Outside the two terminal control cells the entire physical memory agrees
with the contraction's shared-wire memory, including every untouched descriptor. -/
theorem memory_image (f : Fin count → Bool) :
    Agree (workerCell (header pub)) (after src (eventLog (FinalBits.reports w lo f)))
      (equiv F limit S pub cap src phy layout clock room below agree f).val.memory := by
  have run := FinalBits.Worker.stageRun (TerminalProgram.workers F limit S) rfl pub src phy
    layout f cap clock room below valid agree
  rw [← FinalBits.Worker.image pub src layout f]
  exact run.agree

/-- The phase corresponding to a wire assignment returns the chosen bit at every wire address. -/
theorem readback (f : Fin count → Bool) (j : Fin count) :
    (equiv F limit S pub cap src phy layout clock room below agree f).val.memory (lo + j) =
      PrimedInputRAM.encodeBit w (f j) := by
  have data : workerCell (header pub) (lo + j) := by
    have h31 : (header pub + 31).val = (header pub).val + 31 :=
      header_offset pub 31 (by decide) room
    have hj := j.isLt
    unfold workerCell
    omega
  have image := memory_image F limit S pub cap src phy layout clock room below agree valid f
  exact (image _ data).symm.trans (FinalBits.readback lo layout.fits f src j)

omit F limit S valid layout clock room below agree

/-- The linked cost includes the closing call and every transfer of control. -/
theorem probe_cost (f : Fin count → Bool) :
    RAMBuckets.cost Report.probes (reports (header pub) (block pub src phy f).logs) =
      8 * count + 6 := by
  dsimp only [block]
  rw [reports_stageLogs]
  exact FinalBits.Worker.stage_cost pub src f

/-- The data calls have at most seven linked probes and at most 53 physical
events. The same bounds include the closing call. -/
theorem local_caps (f : Fin count → Bool) :
    ∀ r ∈ reports (header pub) (block pub src phy f).logs, r.probes ≤ 7 ∧ r.events.length ≤ 53 := by
  have bounds {e : Entry w} {rs : List (Report w)}
      (h : ∀ r ∈ rs, r.probes ≤ 3 ∧ r.events.length ≤ 23) :
      ∀ t ∈ stageReports (header pub) e rs, t.probes ≤ 7 ∧ t.events.length ≤ 53 := by
    induction rs generalizing e with
    | nil => simp [stageReports]
    | cons r rs ih =>
      intro t ht
      rw [stageReports, List.mem_cons] at ht
      rcases ht with rfl | ht
      · obtain ⟨hp, hl⟩ := h r List.mem_cons_self
        have := report_probes_le (header pub) e r
        have := report_length_le (header pub) e r
        omega
      · exact ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) t ht
  dsimp only [block]
  rw [reports_stageLogs]
  exact bounds (FinalBits.Worker.scan_cost pub count 0 src f).2.2

end PairSimulation.SharedBitPhase

end VPVNP
end Computability
end OAI
