import OAI.Optimization.LinearProgramming.RAM.UniformFootprint
import OAI.Optimization.LinearProgramming.Compression.MinorDetRAM

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

/-- Every high address register, including the descriptors for subsequent requests, survives. -/
theorem determinantBlock_index_frame {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : Memory K → Prop} {s t : Memory K} {k : ℕ} (run : Block.Eval P determinantBlock s k t)
    (p : ℕ) (hp : 16 ≤ p) : t.index p = s.index p := by
  apply run.address_frame_of_list (fun a => decide (a<16)) (by rfl) (by rfl)
  simp [Nat.not_lt_of_ge hp]

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
