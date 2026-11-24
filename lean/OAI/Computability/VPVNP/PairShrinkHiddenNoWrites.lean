import OAI.Computability.VPVNP.PairShrinkHiddenGuess
import OAI.Computability.VPVNP.PairShrinkHiddenSetupNoWrites
import OAI.Computability.VPVNP.CompressorFlowFootprint

/-!
# External memory through a shrinking hidden-field scan

The scan reads the count, resident IDs, and selected term cells. It consumes
the field guesses and stores them privately. Every event sequence preserves
external memory, including an empty scan and arbitrary guessed field values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenGuess

open BurstRAM CompressorRecords SourceTransport

variable {w : ℕ}

/-- One row reads its external headers and writes its guessed bits in the
private bit bank. -/
theorem fieldEvents_noWrites (g : Args w) (m : Memory w) (ptr : ℕ) (e : Row) :
    Writes (fun _ ↦ False) (fieldEvents g m ptr e) := by
  intro a v h
  simp only [fieldEvents, List.mem_append] at h
  rcases h with (head | ticks) | guess
  · simp [Args.header, ShrinkHiddenWidth.events] at head
  · cases List.eq_of_mem_replicate ticks
  · exact (FlowFootprint.bounds_of_noProbes (fun _ ↦ False) (fun _ ↦ False)
      (PrivateFields.events_work (w := w) .guess e.2).2).2 a v guess

/-- Arbitrary guessed fields leave every external word untouched throughout
the count probe, per-field loop and terminating test. -/
theorem events_noWrites (g : Args w) (m : Memory w) (es : List Row) :
    Writes (fun _ ↦ False) (events g m es) := by
  intro a v h
  have scan (ptr : ℕ) (rows : List Row) : Event.write a v ∉ loopEvents g m ptr rows := by
    induction rows generalizing ptr with
    | nil => simp [loopEvents]
    | cons e tail ih =>
      simpa [loopEvents, ih] using
        (show Event.write a v ∉ fieldEvents g m ptr e from fieldEvents_noWrites g m ptr e a v)
  rcases List.mem_append.mp h with setup | loop
  · simp [setupEvents] at setup
  · exact scan _ _ loop

/-- The post-trace external memory agrees at every address with the supplied
memory, regardless of the owner or the encoded field values. -/
theorem after_events (g : Args w) (m : Memory w) (es : List Row) (before : Memory w) :
    after before (events g m es) = before :=
  funext fun _ ↦ after_outside before (events_noWrites g m es) id

end PairSimulation.ShrinkHiddenGuess

end VPVNP
end Computability
end OAI
