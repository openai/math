import OAI.Computability.BorderVNP.CellCQFCost
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Lean.Meta.Tactic.Apply

/-! # Polynomial clocks of the concrete stack library

A procedure's certified clock can be used at the exact input length when the primitive already
has sufficiently small degree. The tactic below unfolds the actual clock, and constructs an
ordinary kernel proof using Mathlib's degree inequalities. Memoization avoids re-proving the
same polynomial estimate for repeated subroutines.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

/-- Evaluate a fixed nonnegative clock with its own coefficient sum and degree. -/
theorem clock_eval_pow (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ p.eval 1*(n+1)^p.natDegree := by
  simp only [Polynomial.eval_eq_sum,Polynomial.sum,one_pow,Nat.mul_one,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left (Nat.le_succ n) i).trans
    (Nat.pow_le_pow_right (by omega) (p.le_natDegree_of_mem_supp i hi))

/-- An actual run bound at an explicit certified clock degree. -/
theorem cost_pow {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (p : Procedure ea eb f) (a : α) {d : ℕ} (h : p.bound.natDegree ≤ d) :
    p.cost a ≤ p.bound.eval 1*((ea a).length+1)^d :=
  (p.cost_le_bound a).trans ((clock_eval_pow ..).trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) h)))

namespace DegreeCertificate

private theorem add (p q : Polynomial ℕ) (i j : ℕ) (h : p.natDegree ≤ i) (k : q.natDegree ≤ j) :
    (p+q).natDegree ≤ max i j := (Polynomial.natDegree_add_le p q).trans (max_le_max h k)

private theorem mul (p q : Polynomial ℕ) (i j : ℕ) (h : p.natDegree ≤ i) (k : q.natDegree ≤ j) :
    (p*q).natDegree ≤ i+j := Polynomial.natDegree_mul_le.trans (Nat.add_le_add h k)

private theorem comp (p q : Polynomial ℕ) (i j : ℕ) (h : p.natDegree ≤ i) (k : q.natDegree ≤ j) :
    (p.comp q).natDegree ≤ i*j := Polynomial.natDegree_comp_le.trans (Nat.mul_le_mul h k)

private theorem power (p : Polynomial ℕ) (i j : ℕ) (h : p.natDegree ≤ i) :
    (p^j).natDegree ≤ j*i := Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left j h)

private theorem c (k : ℕ) : (Polynomial.C k).natDegree ≤ 0 := (Polynomial.natDegree_C _).le

private theorem x : (Polynomial.X : Polynomial ℕ).natDegree ≤ 1 := Polynomial.natDegree_X.le

private theorem numeral (k : ℕ) : (k : Polynomial ℕ).natDegree ≤ 0 := by simp

open Lean Meta Elab Tactic

private def isC (e : Expr) : Bool := e.getAppArgs.any fun a => a.isAppOf ``Polynomial.C

private partial def headClock (e : Expr) : MetaM Expr := do
  let t := e.consumeMData.headBeta
  if isC t || [``Polynomial.X,``HAdd.hAdd,``HMul.hMul,``Polynomial.comp,``HPow.hPow,``OfNat.ofNat].any
      (fun n => t.isAppOf n) then return t
  if let .proj .. := t then
    if let some u ← reduceProj? t then return ← headClock u
  if let .letE _ _ v b _ := t then return ← headClock (b.instantiate1 v)
  if let some u ← unfoldDefinition? t (ignoreTransparency := true) then return ← headClock u
  throwError "expected a certified clock formed from natural polynomials, encountered {t.getAppFn}"

private partial def derive (e : Expr) (cache : IO.Ref (Std.HashMap Expr (Nat × Expr))) :
    MetaM (Nat × Expr) := do
  if let some h := (← cache.get)[e]? then return h
  let t ← headClock e
  let as := t.getAppArgs
  let h ← if isC t then pure (0, mkApp (mkConst ``c) as.back!)
    else if t.isAppOf ``Polynomial.X then pure (1, mkConst ``x)
    else if t.isAppOf ``OfNat.ofNat then pure (0, mkApp (mkConst ``numeral) as[1]!)
    else do
      let a := as[as.size-2]!
      let b := as.back!
      let (i, hi) ← derive a cache
      if t.isAppOf ``HPow.hPow then
        let some j ← getNatValue? b | throwError "expected a constant polynomial exponent"
        pure (j*i,mkAppN (mkConst ``power) #[a,mkNatLit i,b,hi])
      else
        let (j,hj) ← derive b cache
        let (v,decl) := if t.isAppOf ``HAdd.hAdd then (max i j,``add)
          else if t.isAppOf ``HMul.hMul then (i+j,``mul) else (i*j,``comp)
        pure (v,mkAppN (mkConst decl) #[a,b,mkNatLit i,mkNatLit j,hi,hj])
  cache.modify fun m => m.insert e h
  return h

/-- Prove a numeric upper bound on the degree of a concrete stack-program clock. -/
elab (name := cqfDegree) "cqf_degree" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← g.getType
  let some (_,lhs,rhs) := t.le? | throwError "expected a degree inequality"
  unless lhs.isAppOf ``Polynomial.natDegree do throwError "expected a polynomial degree on the left"
  let e := lhs.getAppArgs.back!
  let cache ← IO.mkRef {}
  let (d,proof) ← derive e cache
  let some target ← getNatValue? rhs | throwError "expected a numerical upper bound"
  if d > target then throwError "certified structural degree is {d}; requested {target}"
  let result ← if d == target then pure proof else do
    let small := mkAppN t.getAppFn (t.getAppArgs.set! (t.getAppArgs.size-2) (mkNatLit d))
    let h ← mkDecideProof small
    pure (mkAppN (mkConst ``Nat.le_trans) #[lhs,mkNatLit d,rhs,proof,h])
  g.assign result
  replaceMainGoal []

end DegreeCertificate
end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  clock_eval_pow
  cost_pow)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
