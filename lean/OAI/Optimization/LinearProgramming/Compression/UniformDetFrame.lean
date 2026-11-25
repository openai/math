import OAI.Optimization.LinearProgramming.RAM.UniformFootprint
import OAI.Optimization.LinearProgramming.Compression.UniformDet
import OAI.Optimization.LinearProgramming.Compression.UniformBirdCell

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

private def determinantScratch (p : ℕ) := [2,3,4,5,6,7,8,9,10,13].contains p

/-- The address-bank frame applies to the original safe run itself. -/
theorem uniformDet_address_frame {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : Memory K → Prop} {m t : Memory K} {k : ℕ}
    (run : Block.Eval P (uniformDetBlock uniformBirdCell) m k t) (p : ℕ)
    (hp : p ∉ ({2,3,4,5,6,7,8,9,10,13} : Finset ℕ)) : t.index p = m.index p := by
  apply run.address_frame_of_list determinantScratch (by rfl) (by rfl)
  simpa [determinantScratch] using hp

end Compression
end LinearProgramming
end Optimization
end OAI
