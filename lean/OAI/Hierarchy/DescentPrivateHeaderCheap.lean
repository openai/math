import OAI.Hierarchy.DescentPrivateHeader
import OAI.Hierarchy.ProtocolRAMCheapCode
import Mathlib.Tactic.FinCases

namespace OAI
namespace Hierarchy.DescentPrivateHeader
open ProtocolRAM ThreeFlat.RAM PhysicalProcedure

theorem initialize_cheap (w a : ℕ) : CheapCode (clearHeader w a) := by
  intro P R K pc reg pub exit i
  exact scan_cheap w a 1 (.lit 0) pc reg pub exit i

theorem commit_cheap (w a upper : ℕ) : CheapCode (commit w a upper) := by
  intro p r k pc reg pub exit i
  change Fin 10 at i
  fin_cases i <;> trivial

end Hierarchy.DescentPrivateHeader

end OAI
