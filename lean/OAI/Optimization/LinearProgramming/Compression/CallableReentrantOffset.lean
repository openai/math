import OAI.Optimization.LinearProgramming.Compression.CallableProxyOffset
import OAI.Optimization.LinearProgramming.RAM.CallableReentrant
import OAI.Optimization.LinearProgramming.Compression.SmallProxyTapeLayout

/-! Stage a new offset row from the caller's physical buffers before invoking it. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM RAM.Callable
open scoped BigOperators

/-- A reusable offset invocation on freshly written tapes; all staging and call
instructions are charged and the finite callee allocation is available for the next call. -/
theorem reentrantProxyOffsetFragment_raw {n : ℕ} (fuel prec cap : ℕ) {A : ℤ} (c : ℤ)
    (a : Fin n → ℤ) (mag : Fin n → ℚ) (old caller : Memory ℚ) (P : ℚ → Prop)
    (sb ab : ℕ) (hm : ∀ i, 0 < mag i) (hform : |c| + ∑ i, |a i| ≤ A)
    (hcut : (2 : ℤ)^prec*A ≤ 2^fuel)
    (hq : ∀ q, ratBits q ≤ 3 + 2*((n+2)+(2*(n+1)+3)*(prec+2+fuel+1)) → P q)
    (hc : caller.AllData P) (hold : old.AllData P) (hz : P 0)
    (foot : Footprint cap (old.atPC 0))
    (raw : RawTapes caller sb ab (cap+1)
      (smallProxyScalarTape (2^(prec+2)) c a (fun i => (logProxyNumerator fuel prec (mag i)).getD 0)) [n+1])
    (hcap : 11*(n+1)+42 ≤ cap) :
    let data i := logProxyNumerator fuel prec (mag i)
    let large := Finset.univ.filter (fun i => data i = none)
    let D := (2 : ℕ)^(prec+2)
    let grid i := (data i).getD 0
    ∃ last : Memory ℚ, (Fragment.stage proxyOffsetFragment).Run P (Odd.memory old caller)
        (19*(cap+1)+225+(2*(9*(n+1)+3)+3))
        (Odd.memory last (caller.putData 45 (clearedProxyOffset large D c a grid : ℚ))) ∧
      Footprint cap (last.atPC 0) := by
  let D := (2 : ℕ)^(prec+2)
  let grid (i : Fin n) := (logProxyNumerator fuel prec (mag i)).getD 0
  let xs := smallProxyScalarTape D c a grid
  have hxs : xs.length ≤ cap+1 := by
    rw [show xs.length=2*n+5 from smallProxyScalarTape_length ..]
    omega
  have hd : ([n+1] : List ℕ).length ≤ cap+1 := by simp
  obtain ⟨last,run,foot'⟩ := proxyOffsetFragment_prepared fuel prec c a mag caller P hm hform hcut hq hc
  have staged := Fragment.stage_of_run (old.atPC 0) caller sb ab cap (cap+1) xs [n+1]
    raw hc hold hz foot (Nat.lt_succ_self _) hxs hd run
  exact ⟨last,staged,foot'.mono ((affineEval_callWindow_le (smallProxyLeft D a)
    (smallProxyRight c grid)).trans hcap)⟩

end Compression
end LinearProgramming
end Optimization
end OAI
