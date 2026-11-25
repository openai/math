import OAI.Optimization.LinearProgramming.Lattice.LLLSwap
import HexLLL.Native

/-! The three-quarter decrease for the executable integer LLL pivot at `δ=3/4`.
The swap step is from Kim Morrison's [Hex LLL implementation](https://github.com/leanprover/hex-lll/blob/5676b60afa8401aea99c77091e94152d07e9c222/HexLLL/Native.lean)
(© 2026 Lean FRO, LLC, Apache-2.0). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal

/-- A failing integer Lovász test forces the quantitative potential decrease on the
actual native swap. The proof also works on raw stored states whenever the test fails. -/
theorem native_swapStep_potential_three_quarters {n m : ℕ} (s : LLLState n m) (k : ℕ)
    (hk0 : 0 < k) (hk : k < n)
    (hfail : (4 : ℤ) * ((s.d.get ⟨k+1, by omega⟩ : ℤ) * (s.d.get ⟨k-1, by omega⟩ : ℤ) +
        ((s.ν.getRow ⟨k, hk⟩).get ⟨k-1, by omega⟩) ^ 2) <
      3 * (s.d.get ⟨k, by omega⟩ : ℤ)^2) :
    4 * (s.swapStep k).potential ≤ 3 * s.potential := by
  apply swap_interiorGramPotential s.d (s.swapStep k).d hk0 hk _ _ hfail
  · unfold LLLState.swapStep
    rw [dite_eq_left hk, dite_eq_left hk0]
    exact Vector.getElem_set_self (xs := s.d) (Nat.lt_succ_of_lt hk)
  · intro i hi
    unfold LLLState.swapStep
    rw [dite_eq_left hk, dite_eq_left hk0]
    exact Vector.getElem_set_ne (Nat.lt_succ_of_lt hk) i.isLt (fun h => hi h.symm)
  · positivity

end Lattice
end LinearProgramming
end Optimization
end OAI
