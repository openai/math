import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.RAM.Footprint

/-! Finite scalar and address support after the measured execution of a RAM block. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

/-- After preparation every scalar or address cell outside this explicit window
vanishes, and the value of every address register fits inside the same window. -/
theorem powerPackingStage_footprint {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : K → Prop} {stage : Block} {initial final : Memory K} {k B : ℕ}
    (run : Block.Eval (Memory.AllData P) stage initial k final) (foot : Footprint B (initial.atPC 0)) :
    Footprint (max B (addressBudget (stage.compile 0))+k) (final.atPC 0) := by
  obtain ⟨tr,ht,last,_⟩ := (run.compile_correct (CodeAt.whole (stage.compile 0))).to_trace
  have h := trace_footprint (le_max_right B (addressBudget (stage.compile 0)))
    (foot.mono (le_max_left _ _)) ht (Fin.last k)
  rw [last] at h
  exact ⟨h.address,h.data_zero,h.index_zero⟩

end Compression
end LinearProgramming
end Optimization
end OAI
