import OAI.Optimization.LinearProgramming.Compression.RequestGraphDyadicProbe
import OAI.Optimization.LinearProgramming.Lattice.BitProbeRatios

/-! Construct the first bisection action from the graph-grid row pair. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open _root_.OAI.Optimization.LinearProgramming.Lattice Lattice.Bit

noncomputable def startProbeP : Procedure gridArgCode Driver.Probe.actionCode startProbe := by
  let z := second Nat.bits intRowCode
  let dim := unarySuccessor.comp ((PriceGame.Control.Native.rowSizeP intCode 0).comp z)
  let params := (dim.pair gridDepthP).pair (constant gridArgCode intMatrixCode ([]:IntMatrix))
  let rows := gridRowsP
  let left := (first intRowCode intRowCode).comp rows
  let right := (second intRowCode intRowCode).comp rows
  let singleton := (listCons intRowCode).comp (left.pair (constant gridArgCode intMatrixCode ([]:IntMatrix)))
  let empty := constant gridArgCode Driver.Probe.ratListCode ([]:List ℚ)
  exact Driver.Probe.nextRowP.comp (((params.pair right).pair singleton).pair empty)

end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
