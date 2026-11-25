import Mathlib.Algebra.Polynomial.Eval.Defs
import Lean.Elab.Tactic.Omega

/-! Scalar formulas for the communication clock. Evaluate these identities at symbolic
exponents before substituting the large fixed exponents in the paper. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire
namespace Formula

noncomputable def price (time catalogue grid : ℕ) : Polynomial ℕ :=
  let x : Polynomial ℕ := Polynomial.X
  100*(x+(x*(x^time+1))^catalogue+Polynomial.C grid+1)^3

theorem price_eval (time catalogue grid x : ℕ) :
    (price time catalogue grid).eval x = 100*(x+(x*(x^time+1))^catalogue+grid+1)^3 := by
  simp only [price,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]

noncomputable def query (time branches : ℕ) : Polynomial ℕ :=
  let x : Polynomial ℕ := Polynomial.X
  x^time*(2*(x+1))^branches

theorem query_eval (time branches x : ℕ) :
    (query time branches).eval x = x^time*(2*(x+1))^branches := by
  simp only [query,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]

noncomputable def dialogue (q p : Polynomial ℕ) : Polynomial ℕ :=
  let x := Polynomial.X
  2*q + (6*x+4) + 1 + (2*x+1+x*(2*p+1)) + 1

theorem dialogue_eval (q p : Polynomial ℕ) (x : ℕ) :
    (dialogue q p).eval x = 2*q.eval x+(6*x+4)+1+(2*x+1+x*(2*p.eval x+1))+1 := by
  simp only [dialogue,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one]

theorem roster_growth (n x a b : ℕ) (h : a ≤ b) : (x*(a+1))^n ≤ (x*(b+1))^n :=
  Nat.pow_le_pow_left (Nat.mul_le_mul_left x (Nat.add_le_add_right h 1)) n

theorem input_bounds {n r x c d e : ℕ} (hn : n ≤ x) (hr : r ≤ x) (he : e ≤ c) :
    n ≤ x+c+d ∧ e ≤ x+c+d ∧ r ≤ x+c+d ∧ d ≤ x+c+d := by omega

theorem query_growth {steps limit quantity n x : ℕ} (d : ℕ)
    (h : steps ≤ limit) (f : quantity ≤ n^d) (base : n ≤ x) :
    steps*quantity ≤ limit*x^d := Nat.mul_le_mul h (f.trans (Nat.pow_le_pow_left base d))

theorem packet_total {q top h p cap n x : ℕ}
    (hq : q ≤ top) (hh : h ≤ 6*x+4) (hp : p ≤ cap) (hn : n ≤ x) :
    max (2*q+h+1) (2*n+1+n*(2*p+1)) ≤ 2*top+(6*x+4)+1+(2*x+1+x*(2*cap+1))+1 := by
  have area : n*(2*p+1) ≤ x*(2*cap+1) := Nat.mul_le_mul hn (by omega)
  apply max_le <;> omega

end Formula
end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
