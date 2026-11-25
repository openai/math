module

public import HexLLL.Native
import all HexLLLMathlib.ReductionInvariant

/-! The residue bound for the native tie convention comes from Kim Morrison's
[Hex LLL reduction invariants](https://github.com/leanprover/hex-lll-theory/blob/761108380d7bdae23181785d52703b4883388da1/HexLLLMathlib/ReductionInvariant.lean)
(© 2026 Lean FRO, LLC, Apache-2.0). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal

public theorem native_nearest_residue (a : ℤ) (d : ℕ) (hd : 0 < d) :
    2 * (a - LLLState.nearestQuotient a d * Int.ofNat d).natAbs ≤ d :=
  LLLState.nearestQuotient_residue_bound a d hd

end Lattice
end LinearProgramming
end Optimization
end OAI
