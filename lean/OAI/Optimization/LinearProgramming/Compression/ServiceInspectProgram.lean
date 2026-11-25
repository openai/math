import OAI.Optimization.LinearProgramming.Compression.ServiceIngress
import OAI.Optimization.LinearProgramming.Compression.ServiceCandidateDet
import OAI.Optimization.LinearProgramming.Compression.ServiceLookupProgram
import OAI.Optimization.LinearProgramming.Compression.ServiceSlotCompare
import OAI.Optimization.LinearProgramming.Compression.ServiceGather

/-! The request, determinant lookup and gathered solver input use the same program over both scalar fields. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

/-- The common prefix of both the successful reply and the restart path. -/
def inspectRequest (cmp : Block) : Block := .seq Ingress.stageRequest (.seq candidateDet (lookup cmp))

/-- The public input convention is consumed once. The target and all existing generator
magnitudes are then available in the compact solver tape. -/
def inspectAndGather : Block := .seq (inspectRequest slotCompare) gatherMagnitudes

/-- The per-request time is a single fixed dimension polynomial for all online histories. -/
theorem inspectTime_bound (n g : ℕ) (h : g ≤ (n+1)^6) : 3000*(g+1)*(n+1)^7 ≤ 6000*(n+1)^13 := calc
  _ ≤3000*((n+1)^6+1)*(n+1)^7 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.succ_le_succ h))
  _ ≤_ := by ring_nf;omega

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
