import OAI.Optimization.LinearProgramming.Lattice.BitArithmetic
import HexLLL.Native

/-! These identities relate the bit-stack scalar procedures to the integer arithmetic in
Kim Morrison's [Hex LLL implementation](https://github.com/leanprover/hex-lll/blob/5676b60afa8401aea99c77091e94152d07e9c222/HexLLL/Native.lean)
(© 2026 Lean FRO, LLC, Apache-2.0). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

theorem nearest_native (a : ℤ) (d : ℕ) :
    nearest (a,d) = Hex.Internal.LLLState.nearestQuotient a d := rfl

theorem gramNumerator_int (g : GramQuad) :
    (gramNumerator g : ℤ) = (g.1.1 : ℤ) * g.2.1 + g.2.2 ^ 2 := by
  simp [gramNumerator, ← sq, sq_abs]

theorem lovasz_true_iff (g : GramQuad) :
    lovasz g = true ↔
      (3/4 : ℚ).num * (g.1.2 : ℤ)^2 ≤ ((3/4 : ℚ).den : ℤ) * ((g.1.1 : ℤ)*g.2.1 + g.2.2^2) := by
  simp only [lovasz, decide_eq_true_eq]
  rw [← gramNumerator_int, show (3/4 : ℚ).num = (3 : ℤ) by norm_num,
    show (3/4 : ℚ).den = (4 : ℕ) by norm_num, pow_two]
  exact_mod_cast Iff.rfl

theorem swappedGram_native (g : GramQuad) :
    swappedGram g = ((((g.1.1 : ℤ)*g.2.1 + g.2.2^2) / (g.1.2 : ℤ)).toNat) := by
  rw [← gramNumerator_int]
  simp [swappedGram, ← Int.natCast_ediv]

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
