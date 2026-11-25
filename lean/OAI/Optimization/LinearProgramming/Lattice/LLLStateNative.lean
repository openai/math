module
public import HexLLL.Native
import all HexLLLMathlib.ReductionInvariant

/-! The reducer's verified swap-state invariant, used when bounding the number of
iterations of its executable loop. The swap invariant is from Kim Morrison's
[Hex LLL formalization](https://github.com/leanprover/hex-lll-theory/blob/761108380d7bdae23181785d52703b4883388da1/HexLLLMathlib/ReductionInvariant.lean)
(© 2026 Lean FRO, LLC, Apache-2.0). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal

/-- The stored Gram determinants and scaled coefficients retain their interpretations
after the native adjacent swap of an independent valid state. -/
public theorem native_swap_preserves_valid {n m : ℕ} (s : LLLState n m) (k : ℕ)
    (hI : s.b.independent) (hV : s.Valid) : (s.swapStep k).Valid := by
  exact Hex.Internal.LLLState.swapStep_valid s k hI hV

end Lattice
end LinearProgramming
end Optimization
end OAI
