import OAI.Optimization.LinearProgramming.RAM.CallableReentrant
import OAI.Optimization.LinearProgramming.Compression.CallableDirectProxy

/-! A reusable minor-log oracle over the staged raw inputs. Every stage and native
instruction is counted. Its entry and exit use the same finite callee-memory bound. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM RAM.Callable
open scoped BigOperators

def reentrantProxySignFragment (dest : TagSink) : Fragment := Fragment.stage (directProxySignFragment dest)

theorem reentrantProxySignFragment_raw {n : ℕ} (fuel prec B D : ℕ) {A : ℤ}
    (c : ℤ) (a : Fin n → ℤ) (mag : Fin n → ℚ) (old caller : Memory ℚ) (P : ℚ → Prop)
    (dest : TagSink) (sb ab : ℕ) (hm : ∀ i, 0 < mag i) (hbits : ∀ i, ratBits (mag i) ≤ B)
    (hform : |c| + ∑ i, |a i| ≤ A) (hcut : (2 : ℤ)^prec * A ≤ 2^fuel)
    (hq : ∀ q, ratBits q ≤ proxyQueryBits n fuel prec B → P q) (hc : caller.AllData P)
    (hold : old.AllData P) (hz : P 0) (foot : Footprint D (old.atPC 0))
    (hr : ∀ tag<3, (dest.store tag caller).AllData P)
    (hflag : caller.index 61 = (preparedProxyQuery fuel prec c a mag).symbolic.toNat)
    (hzero : caller.index 62 = 0)
    (raw : let p := preparedProxyQuery fuel prec c a mag
      RawTapes caller sb ab (D+1) p.scalar p.address)
    (hwindow : directProxyWindow (preparedProxyQuery fuel prec c a mag) + proxyQuerySteps n fuel ≤ D) :
    let form := (c : ℝ) + ∑ i, (a i : ℝ) * logProxyValue prec (mag i)
      (logProxyNumerator fuel prec (mag i))
    let tag : ℕ := if form<0 then 0 else if 0<form then 2 else 1
    ∃ last : Memory ℚ, (reentrantProxySignFragment dest).Run P
      (Odd.memory old caller) (19*(D+1)+225+(2*proxyQuerySteps n fuel+4))
      (Odd.memory last (dest.store tag caller)) ∧ Footprint D (last.atPC 0) := by
  let p := preparedProxyQuery fuel prec c a mag
  have hd : directProxyWindow p ≤ D := (Nat.le_add_right _ _).trans hwindow
  have hw : nativeWindow literalPowerCompareProgram p.address p.scalar ≤ D := (le_max_left ..).trans hd
  have hs : p.scalar.length ≤ D+1 :=
    (le_max_left ..).trans ((le_max_right ..).trans (Nat.le_succ_of_le hw))
  have ha : p.address.length ≤ D+1 :=
    (le_max_left ..).trans ((le_max_right ..).trans ((le_max_right ..).trans (Nat.le_succ_of_le hw)))
  obtain ⟨last,run,foot'⟩ := directProxySignFragment_prepared fuel prec B c a mag caller P dest
    hm hbits hform hcut hq hc hr hflag hzero
  exact ⟨last,Fragment.stage_of_run (old.atPC 0) caller sb ab D (D+1) p.scalar p.address raw
    hc hold hz foot (Nat.lt_succ_self _) hs ha run,foot'.mono hwindow⟩

end Compression
end LinearProgramming
end Optimization
end OAI
