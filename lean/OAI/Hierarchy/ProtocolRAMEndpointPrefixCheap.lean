import OAI.Hierarchy.ProtocolRAMEndpointPrefix
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Admissible native opcodes of both stages of the exclusive prefix sum -/

namespace Hierarchy.ProtocolRAMRankCheap
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open ProtocolRAM

set_option maxRecDepth 8192 in
theorem site_prefix (w counts starts n : ℕ) : CheapCode (ProtocolRAMEndpointPrefix.accumulate w counts starts n) := by
  intro P R K pc reg pub exit i
  change Fin 14 at i
  fin_cases i <;> trivial

theorem exclusive_cheap (w counts starts n : ℕ) : CheapCode (ProtocolRAMEndpointPrefix.exclusive w counts starts n) :=
  cheap_seq (writing_cheap (.literal 0 : Term w 0 1) Fin.elim0 starts 1 ⟨trivial,trivial⟩) (site_prefix w counts starts n)

end Hierarchy.ProtocolRAMRankCheap

end OAI
