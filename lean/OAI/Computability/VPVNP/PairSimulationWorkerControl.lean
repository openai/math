import OAI.Computability.VPVNP.PairSimulationTerminalBlocks

/-! # Single-worker frames at native terminal burst boundaries -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink
open BurstRAM LiveProgram CompressorRecords

variable {w : ℕ} (workers : Stage → PairTable) (pub : Fin 11 → Word w) (cap : ℕ)

/-- Address frame for every successful single worker burst, with the actual
controller writes applied before the next burst. -/
structure WorkerControl (s : Stage) (a : ℕ) (m : Memory w) where
  /-- Invariant on a worker's persistent state word and memory at burst boundaries, established
  at state zero and propagated by returning bursts after controller writes. -/
  inv : Word w → Memory w → Prop
  ready : inv 0 m
  advance : ∀ (st : Word w) (mem : Memory w) (bits : List Bool) (rep : Report w),
    inv st mem →
    execute (source workers s pub) (rawFuel pub cap (.resume s st)) ((source workers s pub).start st) mem bits =
      some rep →
    let out := after mem (report (header pub) (.resume s st) rep).events
    out a = mem a ∧ ∀ st', rep.result = some st' → inv st' out

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
