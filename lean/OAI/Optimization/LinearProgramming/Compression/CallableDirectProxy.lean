import OAI.Optimization.LinearProgramming.RAM.CallableControl
import OAI.Optimization.LinearProgramming.RAM.CallableOddCalls
import OAI.Optimization.LinearProgramming.RAM.CallableWindow
import OAI.Optimization.LinearProgramming.Compression.ProxyQueryRAM

/-! Native comparison of a raw minor-log query at a reentrant call site. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM RAM.Callable
open scoped BigOperators

/-- Logical address 61 identifies a symbolic query. Logical address 62 holds zero.
The numerical payload is the branch's ordinary pair of raw input tapes. -/
def directProxySignFragment (dest : TagSink) : Fragment :=
  Fragment.branch (Odd.cond (.addrLT 62 61))
    (Fragment.invoke literalPowerCompareProgram 3 (Odd.sink dest))
    (Fragment.invoke smallAffineProgram 3 (Odd.sink dest))

/-- A common bound for the two native branches' initially accessible addresses. -/
def directProxyWindow (p : ProxyQueryTapes) : ℕ :=
  max (nativeWindow literalPowerCompareProgram p.address p.scalar)
    (nativeWindow smallAffineProgram p.address p.scalar)

/-- Return the full ternary comparison, or any fixed recoding of it, through `dest`.
Every caller memory cell except the logical return register is preserved. The callee's
dirty output is bounded for the next invocation of the staging loop. -/
theorem directProxySignFragment_prepared {n : ℕ} (fuel prec B : ℕ) {A : ℤ}
    (c : ℤ) (a : Fin n → ℤ) (mag : Fin n → ℚ) (caller : Memory ℚ) (P : ℚ → Prop)
    (dest : TagSink) (hm : ∀ i, 0 < mag i) (hbits : ∀ i, ratBits (mag i) ≤ B)
    (hform : |c| + ∑ i, |a i| ≤ A) (hcut : (2 : ℤ)^prec * A ≤ 2^fuel)
    (hq : ∀ q, ratBits q ≤ proxyQueryBits n fuel prec B → P q) (hc : caller.AllData P)
    (hr : ∀ tag<3, (dest.store tag caller).AllData P)
    (hflag : caller.index 61 = (preparedProxyQuery fuel prec c a mag).symbolic.toNat)
    (hzero : caller.index 62 = 0) :
    let p := preparedProxyQuery fuel prec c a mag
    let form := (c : ℝ) + ∑ i, (a i : ℝ) * logProxyValue prec (mag i)
      (logProxyNumerator fuel prec (mag i))
    let tag : ℕ := if form<0 then 0 else if 0<form then 2 else 1
    ∃ last : Memory ℚ, (directProxySignFragment dest).Run P
      (Odd.memory (start p.address p.scalar).memory caller) (2*proxyQuerySteps n fuel+4)
      (Odd.memory last (dest.store tag caller)) ∧
      Footprint (directProxyWindow p + proxyQuerySteps n fuel) (last.atPC 0) := by
  classical
  let p := preparedProxyQuery fuel prec c a mag
  let form := (c : ℝ) + ∑ i, (a i : ℝ) * logProxyValue prec (mag i)
    (logProxyNumerator fuel prec (mag i))
  let tag : ℕ := if form<0 then 0 else if 0<form then 2 else 1
  have ht : tag<3 := by dsimp [tag]; split_ifs <;> decide
  have flag : caller.index 61 = p.symbolic.toNat := hflag
  obtain ⟨k,hk,tr,htape,ho,hs⟩ := proxySignBranch_correct fuel prec B c a mag hm hbits hform hcut
  let selected := if p.symbolic then literalPowerCompareProgram else smallAffineProgram
  have native : Trace selected (start p.address p.scalar) k tr := htape
  have sub := Odd.invoke_packed 3 dest P caller p.address p.scalar tr ht hc native
    (fun i j => hq _ (hs i j)) ho (hr tag ht)
  have window : nativeWindow selected p.address p.scalar ≤ directProxyWindow p := by
    cases hb : p.symbolic with
    | false =>
      rw [show selected=smallAffineProgram by simp [selected,hb]]
      exact le_max_right _ _
    | true =>
      rw [show selected=literalPowerCompareProgram by simp [selected,hb]]
      exact le_max_left _ _
  have hf := (nativeWindow_trace native hk).mono (Nat.add_le_add_right window _)
  refine ⟨_,?_,hf⟩
  cases hb : p.symbolic with
  | false =>
    have guard : (Odd.cond (.addrLT 62 61)).test (Odd.memory (start p.address p.scalar).memory caller) = false := by
      rw [Odd.cond_test]
      simp [Cond.test,flag,hzero,hb]
    have run := Fragment.Run.branchFalse guard (Fragment.invoke literalPowerCompareProgram 3 (Odd.sink dest))
      (show (Fragment.invoke smallAffineProgram 3 (Odd.sink dest)).Run _ _ _ _ from by simpa [selected,hb] using sub)
    exact run.mono (by omega)
  | true =>
    have guard : (Odd.cond (.addrLT 62 61)).test (Odd.memory (start p.address p.scalar).memory caller) = true := by
      rw [Odd.cond_test]
      simp [Cond.test,flag,hzero,hb]
    have run := Fragment.Run.branchTrue guard
      (show (Fragment.invoke literalPowerCompareProgram 3 (Odd.sink dest)).Run _ _ _ _ from by simpa [selected,hb] using sub)
      (Fragment.invoke smallAffineProgram 3 (Odd.sink dest))
    exact run.mono (by omega)

end Compression
end LinearProgramming
end Optimization
end OAI
