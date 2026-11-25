import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Cheap native opcodes for generated sparse writes -/

namespace Hierarchy.ProtocolRAMRankCheap
open ProtocolRAM

set_option maxRecDepth 8192 in
theorem indexed (w addresses words n : ℕ) : CheapCode (ProtocolRAMIndexedWrite.scatter w addresses words n) := by
  intro P R K pc reg pub exit i
  change Fin 12 at i
  fin_cases i <;> trivial

theorem generated (w addresses words n : ℕ) (a v : Expr) :
    CheapCode (ProtocolRAMGeneratedWrite.program w addresses words n a v) :=
  cheap_seq (cheap_seq (scan_cheap w addresses n a) (scan_cheap w words n v))
    (indexed w addresses words n)

end Hierarchy.ProtocolRAMRankCheap

end OAI
