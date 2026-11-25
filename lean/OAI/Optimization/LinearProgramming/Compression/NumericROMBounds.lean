import Mathlib.Tactic.GCongr
import OAI.Optimization.LinearProgramming.Compression.ProxyNumericComplexity
import OAI.Optimization.LinearProgramming.Compression.SignWirePolynomial
import OAI.Optimization.LinearProgramming.Compression.TaggedClock
import OAI.Optimization.LinearProgramming.Compression.InnerCostEnvelope

/-! ## Uniform polynomial clocks, scalar heights and physical window for the numerical minor ROM

Only the scalar-height polynomial takes the total input bit length. The operation count
and address capacities depend on the dimension and the fixed finite ROM. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace NumericROM

open RAM SignWire Polynomial
open Inner.Cost (eval_nat_mono)

noncomputable def effectiveB (n B k : ℕ) : ℕ := max B (max (numericProxyCacheBits n B) (2*k+7))

private theorem input_le_comparatorBits (d fuel prec b : ℕ) : b ≤ wordComparatorBits d fuel prec b := by
  unfold wordComparatorBits symbolicQueryBits proxyQueryBits
  apply le_trans _ (le_max_left _ _)
  apply le_trans _ (le_max_left _ _)
  apply le_trans _ (le_max_right _ _)
  have sq : b≤b^2 := Nat.le_self_pow (by decide) b
  omega

/-- One common scalar policy supports the original inputs, the cache and the returned
signed rational word. It remains sufficient on every branch of the sign handler. -/
theorem height_dominates (n B k d fuel prec : ℕ) :
    let h := wordComparatorBits d fuel prec (effectiveB n B k)
    B≤h ∧ numericProxyCacheBits n B≤h ∧ 2*k+7≤h := by
  have inclusion := input_le_comparatorBits d fuel prec (effectiveB n B k)
  exact ⟨(le_max_left ..).trans inclusion,((le_max_left ..).trans (le_max_right ..)).trans inclusion,
    ((le_max_right ..).trans (le_max_right ..)).trans inclusion⟩

private noncomputable def arity : Polynomial ℕ := (X+1)^6+1
private noncomputable def eff (P : Polynomial ℕ) : Polynomial ℕ := X+numericCacheBitsPolynomial+2*P+7

noncomputable def height (P : Polynomial ℕ) : Polynomial ℕ :=
  100*(arity+manuscriptProxyFuelPolynomial+parameterGridExponent+eff P+1)^3

private theorem arity_le {n g : ℕ} (hg : g≤paperWidth n) : g+1≤arity.eval n := by
  simpa [arity,paperWidth] using Nat.add_le_add_right hg 1

private theorem eff_le (P : Polynomial ℕ) (n B : ℕ) : effectiveB n B (P.eval n) ≤ (eff P).eval (n+B) := by
  have hc := numericProxyCacheBits_le n B
  have hp : P.eval n ≤ P.eval (n+B) := eval_nat_mono P (Nat.le_add_right n B)
  unfold effectiveB
  simp [eff]
  omega

theorem height_le (P : Polynomial ℕ) (n B g : ℕ) (hg : g≤paperWidth n) :
    wordComparatorBits (g+1) (manuscriptProxyFuel n) (paperRadius n+7) (effectiveB n B (P.eval n)) ≤
      (height P).eval (n+B) := by
  let v := n+B
  have hn : n≤v := by dsimp [v]; omega
  have hd : g+1 ≤ arity.eval v := (arity_le hg).trans (eval_nat_mono arity hn)
  have hf : manuscriptProxyFuel n ≤ manuscriptProxyFuelPolynomial.eval v := by
    simpa only [manuscriptProxyFuelPolynomial_eval] using eval_nat_mono manuscriptProxyFuelPolynomial hn
  have hp : paperRadius n+7 ≤ parameterGridExponent.eval v := by
    simpa only [parameterGridExponent_eval,paperRadius] using eval_nat_mono parameterGridExponent hn
  have he : effectiveB n B (P.eval n) ≤ (eff P).eval v := eff_le P n B
  have args := wordComparatorBits_le_poly (g+1) (manuscriptProxyFuel n) (paperRadius n+7) (effectiveB n B (P.eval n))
  apply args.trans
  simp only [RAM.polyBound,height,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_one,Polynomial.eval_ofNat]
  change 100*(_+1)^3 ≤ 100*(arity.eval v+manuscriptProxyFuelPolynomial.eval v+parameterGridExponent.eval v+(eff P).eval v+1)^3
  gcongr

noncomputable def callbackTime : Polynomial ℕ :=
  C (80*fixedProxyAddressBudget+1220300)*(arity+manuscriptProxyFuelPolynomial+1)^4

theorem callbackTime_le (n g : ℕ) (hg : g≤paperWidth n) :
    wordComparatorTime (g+1) (manuscriptProxyFuel n) (symbolicQueryCap (g+1) (manuscriptProxyFuel n)) ≤ callbackTime.eval n := by
  apply (wordComparatorTime_le_poly _ _).trans
  simp only [RAM.polyBound,callbackTime,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_one,manuscriptProxyFuelPolynomial_eval]
  have hd := arity_le hg
  gcongr

private noncomputable def tagCost (P : Polynomial ℕ) : Polynomial ℕ :=
  2*P*(16*P+17)+2*P*(16*P+18)+76*P+205

noncomputable def time (setup P : Polynomial ℕ) (states : ℕ) : Polynomial ℕ :=
  setup+(C (2*states+64)+callbackTime)*P+2+(13*P+7)+tagCost P

/-- The VM clock and all callback and return clocks share a size-independent bound in
`n`, even for inputs that have exceptionally many coefficient bits. -/
theorem time_le (setup P : Polynomial ℕ) (states n g steps len : ℕ) (hg : g≤paperWidth n)
    (hs : steps≤P.eval n) (hl : len≤P.eval n) :
    setup.eval n+(2*states+64+wordComparatorTime (g+1) (manuscriptProxyFuel n)
      (symbolicQueryCap (g+1) (manuscriptProxyFuel n)))*steps+2+(13*len+7)+taggedReplyClock len ≤
        (time setup P states).eval n := by
  have cb := callbackTime_le n g hg
  have tag : taggedReplyClock len ≤ (tagCost P).eval n := by
    simp [tagCost,taggedReplyClock]
    gcongr
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_ofNat]
  gcongr

private theorem cache_le_callback (d fuel cap : ℕ) : cachedProxySignSteps d fuel cap ≤ wordComparatorTime d fuel cap := by
  unfold wordComparatorTime numericalTagCost isolatedCachedCost
  omega

/-- The largest physical query address also fits inside the callback majorant. -/
theorem queryCap_le (n g : ℕ) (hg : g≤paperWidth n) :
    symbolicQueryCap (g+1) (manuscriptProxyFuel n) ≤ callbackTime.eval n := by
  let d := g+1
  let f := manuscriptProxyFuel n
  let cap := symbolicQueryCap d f
  have scale : cap≤symbolicQuerySteps d f cap := by unfold symbolicQuerySteps; omega
  have h : cap≤cachedProxySignSteps d f cap := (show cap≤1+symbolicQuerySteps d f cap+1 by omega).trans (le_max_left ..)
  exact h.trans ((cache_le_callback d f cap).trans (callbackTime_le n g hg))

/-- Room for an arbitrary callback schedule and the complete generator row port. -/
noncomputable def window (R P : Polynomial ℕ) : Polynomial ℕ :=
  2*(R+(P+1)*(callbackTime+5))+135+2*(R+(X+1)^6+2)

theorem window_le (R P : Polynomial ℕ) (n g rowBase : ℕ) (hg : g≤paperWidth n) (hr : rowBase≤R.eval n) :
    2*(R.eval n+(P.eval n+1)*(cachedProxySignSteps (g+1) (manuscriptProxyFuel n)
      (symbolicQueryCap (g+1) (manuscriptProxyFuel n))+5))+135+2*(rowBase+g+2) ≤ (window R P).eval n := by
  have cb := (cache_le_callback (g+1) (manuscriptProxyFuel n) _).trans (callbackTime_le n g hg)
  change g≤(n+1)^6 at hg
  simp only [window,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,Polynomial.eval_ofNat,
    Polynomial.eval_pow,Polynomial.eval_X]
  gcongr

end NumericROM
end Compression
end LinearProgramming
end Optimization
end OAI
