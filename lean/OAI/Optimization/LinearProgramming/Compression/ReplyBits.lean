import OAI.Optimization.LinearProgramming.Compression.AdaptiveRequests
import OAI.Optimization.LinearProgramming.RAM.Basic

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- A successful reply has dimension-polynomial binary length even though the bound
on its magnitude is exponential. Here `p` bounds the logarithms of its component heights. -/
theorem reply_ratBits_le {q : ℚ} {p : ℕ}
    (hn : q.num.natAbs ≤ 2^p) (hd : q.den ≤ 2^p) : RAM.ratBits q ≤ 3+2*p := by
  have h (v : ℕ) (hv : v ≤ 2^p) : v.log2 ≤ p := by
    by_cases h0 : v=0
    · simp [h0]
    · exact Nat.le_of_lt_succ ((Nat.log2_lt h0).mpr (hv.trans_lt
        (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self p))))
  unfold RAM.ratBits
  have h₁ := h _ hn
  have h₂ := h _ hd
  omega

theorem ValidMinorAssignment.output_bits {ι : Type*} [Fintype ι] {N : ℕ}
    {l : ι → ℝ} {f : ι → ℚ} (hf : ValidMinorAssignment N l f) (u : ι) :
    RAM.ratBits (f u) ≤ 3+2*onlineMinorBitPolynomial.eval N :=
  reply_ratBits_le (hf.1 u).2.1 (hf.1 u).2.2

end Compression
end LinearProgramming
end Optimization
end OAI
