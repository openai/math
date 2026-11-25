import OAI.Optimization.LinearProgramming.Compression.CachedForms
import OAI.Optimization.LinearProgramming.Lattice.QueryWire

/-! Public word and coefficient interface of the cached logarithm comparator. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open OracleSpec

noncomputable def formOrdering (x : ℝ) : Ordering := if x<0 then .lt else if 0<x then .gt else .eq

noncomputable def cachedWordOracle (n fuel prec : ℕ) (mag : ℕ → ℚ) : WordOracle :=
  Lattice.wordSignOracle (fun row : Fin (n+1) → ℤ =>
    formOrdering (DyadicRAM.cachedForm fuel prec mag row))

def AllowedSignPacket (n calls : ℕ) (A : ℤ) (p : BitProgram) (c : p.Config) (_ : Fin p.states) : Prop :=
  c.transcript.length < calls ∧ ∃ row : Fin (n+1) → ℤ,
    c.bufferRev.reverse=Lattice.signRowWord row ∧ DyadicRAM.coefficientBudget A row

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
