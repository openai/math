import OAI.Optimization.LinearProgramming.RAM.CallableScalarReturn
import OAI.Optimization.LinearProgramming.Compression.ProxyOffsetMachine

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM RAM.Callable
open scoped BigOperators

/-- A mixed affine query returns its cleared constant to the logical caller in scalar 45. -/
def proxyOffsetFragment : Fragment := scalarResultCall affineEvalProgram 0 45

/-- A fixed linear number of native registers covers every call to the affine kernel,
irrespective of the scalar values written in its two input vectors. -/
theorem affineEval_callWindow_le {n : ℕ} (a x : Fin n → ℚ) :
    nativeWindow affineEvalProgram [n] (0 :: 0 :: 0 :: affineInputPairs a x) + (9*n+3) ≤ 11*n+42 := by
  have haddr : addressBudget affineEvalProgram = 39 := by decide
  simp only [nativeWindow,haddr,List.length_cons,List.length_nil,List.sum_cons,List.sum_nil,
    Nat.add_zero,affineInputPairs_length]
  omega

/-- The canonical offset caller consumes D,c and the aligned coefficient/grid stream.
It returns only the computed integer to logical scalar 45, retaining the native final
footprint needed to prepare the exponent writer on the next call. -/
theorem proxyOffsetFragment_prepared {n : ℕ} (fuel prec : ℕ) {A : ℤ} (c : ℤ)
    (a : Fin n → ℤ) (mag : Fin n → ℚ) (caller : Memory ℚ) (P : ℚ → Prop)
    (hm : ∀ i, 0 < mag i) (hform : |c| + ∑ i, |a i| ≤ A)
    (hcut : (2 : ℤ)^prec*A ≤ 2^fuel)
    (hq : ∀ q, ratBits q ≤ 3 + 2*((n+2)+(2*(n+1)+3)*(prec+2+fuel+1)) → P q)
    (hc : caller.AllData P) :
    let data i := logProxyNumerator fuel prec (mag i)
    let large := Finset.univ.filter (fun i => data i = none)
    let D := (2 : ℕ)^(prec+2)
    let grid i := (data i).getD 0
    let input := 0 :: 0 :: 0 :: affineInputPairs (smallProxyLeft D a) (smallProxyRight c grid)
    ∃ last : Memory ℚ, proxyOffsetFragment.Run P (Odd.memory (start [n+1] input).memory caller)
        (2*(9*(n+1)+3)+3) (Odd.memory last (caller.putData 45 (clearedProxyOffset large D c a grid : ℚ))) ∧
      Footprint (nativeWindow affineEvalProgram [n+1] input + (9*(n+1)+3)) (last.atPC 0) := by
  obtain ⟨tr,ht,ho,hv,hs⟩ := computedProxyOffsetRAM fuel prec c a mag hm hform hcut
  obtain ⟨run,foot⟩ := scalarResultCall_prepared 0 45 caller P hc ht ho (fun i j => hq _ (hs i j))
  exact ⟨_,hv ▸ run,foot⟩

end Compression
end LinearProgramming
end Optimization
end OAI
