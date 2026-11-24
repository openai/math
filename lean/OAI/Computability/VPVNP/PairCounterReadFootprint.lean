import OAI.Computability.VPVNP.PairSimulationCounters
import OAI.Computability.VPVNP.CompressorSourceTransport

/-! # The external reads of the native histogram flush -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.Counters

open BurstRAM CompressorRecords.SourceTransport
open private componentEvents word val_word from OAI.Computability.VPVNP.PairSimulationCounters

/-- The flush reads each external component of the designated histogram suffix. -/
theorem events_reads {w : ℕ} (priv : Word w → Word w) (m : Memory w) (src dst n : ℕ)
    (fit : dst+n < 2^w) (allow : ℕ → Prop) (cells : ∀ i : Fin n, allow (dst+i.val)) :
    Reads allow (events priv m src dst n) := by
  induction n generalizing src dst m with
  | zero =>
    intro a v read
    simp [events] at read
  | succ n ih =>
    intro a v read
    rcases List.mem_append.mp read with head | rest
    · simp only [componentEvents, List.mem_cons, List.not_mem_nil, reduceCtorEq,
        Event.read.injEq, false_or, or_false] at head
      rw [head.1, val_word (by omega)]
      exact cells 0
    · apply ih _ (src+1) (dst+1) (by omega) _ a v rest
      intro i
      have h := cells ⟨i.val+1, by omega⟩
      simpa only [Nat.add_assoc, Nat.add_comm 1] using h

end PairSimulation.Counters

end VPVNP
end Computability
end OAI
