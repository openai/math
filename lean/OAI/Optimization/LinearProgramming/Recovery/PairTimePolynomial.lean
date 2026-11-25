import OAI.Optimization.LinearProgramming.Compression.InnerCostEnvelope
import Mathlib.Tactic.GCongr

/-! A polynomial time bound for recovery calls with a fixed polynomial budget
for their register setup. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder

open Polynomial

private noncomputable def scalePolynomial : Polynomial ℕ := 2*X+2
private noncomputable def workerPolynomial : Polynomial ℕ := 6000000*scalePolynomial^9
private noncomputable def capacityPolynomial (reserve : ℕ) : Polynomial ℕ :=
  X+C reserve+workerPolynomial+scalePolynomial^2+2*scalePolynomial+4
private noncomputable def limitPolynomial (reserve : ℕ) : Polynomial ℕ :=
  X+capacityPolynomial reserve+3

/-- The metadata budget is kept in composition form. -/
noncomputable def timePolynomialFor (reserve : ℕ) (header : Polynomial ℕ) : Polynomial ℕ :=
  8*header.comp (limitPolynomial reserve) +
    3*(19*capacityPolynomial reserve+225+(2*workerPolynomial+2)) + 3*(21*X*X+7)

theorem timePolynomialFor_bound (reserve : ℕ) (header : Polynomial ℕ) (h n scratch previous : ℕ) :
    let a := h+2*n+2
    let worker := 6000000*a^9
    let cap := previous+reserve+worker+a^2+2*a+4
    8*header.eval (h+n+scratch+cap+3) +
      3*(19*cap+225+(2*worker+2)) + 3*(21*n*n+7) ≤
      (timePolynomialFor reserve header).eval (h+n+scratch+previous) := by
  let N := h+n+scratch+previous
  let a := h+2*n+2
  let worker := 6000000*a^9
  let cap := previous+reserve+worker+a^2+2*a+4
  have hn : n≤N := by dsimp [N]; omega
  have hprev : previous≤N := by dsimp [N]; omega
  have hinput : h+n+scratch≤N := by dsimp [N]; omega
  have ha : a≤scalePolynomial.eval N := by
    simp only [scalePolynomial,eval_add,eval_mul,eval_ofNat,eval_X]
    dsimp [N,a]; omega
  have hw : worker≤workerPolynomial.eval N := by
    simp only [workerPolynomial,eval_mul,eval_pow,eval_ofNat]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ha 9)
  have hc : cap≤(capacityPolynomial reserve).eval N := by
    dsimp only [cap]
    simp only [capacityPolynomial,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_ofNat]
    gcongr
  have hl : h+n+scratch+cap+3≤(limitPolynomial reserve).eval N := by
    simp only [limitPolynomial,eval_add,eval_X,eval_ofNat]
    omega
  have hm : header.eval (h+n+scratch+cap+3) ≤ header.eval ((limitPolynomial reserve).eval N) :=
    Compression.Inner.Cost.eval_nat_mono header hl
  change 8*header.eval (h+n+scratch+cap+3)+3*(19*cap+225+(2*worker+2))+3*(21*n*n+7) ≤
    (timePolynomialFor reserve header).eval N
  simp only [timePolynomialFor,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat]
  gcongr

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
