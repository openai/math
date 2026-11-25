import OAI.Hierarchy.ProtocolRAMEndpointSort
import OAI.Hierarchy.ProtocolRAMEndpointPrefixCheap

namespace OAI
/-! # Native opcodes in the stable counting sort -/

namespace Hierarchy.ProtocolRAMRankCheap
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open ProtocolRAM

set_option maxRecDepth 8192 in
theorem site_count (w src base n : ℕ) : CheapCode (ProtocolRAMScalarCounts.counting w src base n) := by
  intro P R K pc reg pub exit i
  change Fin 13 at i
  fin_cases i <;> trivial

set_option maxRecDepth 8192 in
theorem site_scatter (w src bins out n : ℕ) : CheapCode (ProtocolRAMEndpointScatter.scatter w src bins out n) := by
  intro P R K pc reg pub exit i
  change Fin 16 at i
  fin_cases i <;> trivial

theorem endpoint_sort (L : ProtocolRAMEndpointSort.Layout) (w n sites : ℕ) :
    CheapCode (ProtocolRAMEndpointSort.program L w n sites) := by
  have counts : CheapCode (ProtocolRAMSiteCounts.program w L.src L.counts n sites) :=
    cheap_seq (writing_cheap (.literal 0 : Term w 0 1) Fin.elim0 L.counts sites ⟨trivial,trivial⟩)
      (site_count w L.src L.counts n)
  unfold ProtocolRAMEndpointSort.program
  exact @cheap_seq w _ _ (@cheap_seq w _ _ counts (exclusive_cheap w L.counts L.starts sites))
    (site_scatter w L.src L.starts L.sorted n)


end Hierarchy.ProtocolRAMRankCheap

end OAI
