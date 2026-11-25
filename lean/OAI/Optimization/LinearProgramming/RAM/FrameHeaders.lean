import OAI.Optimization.LinearProgramming.PrimalDual.RAMBudget
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Assemble fixed address-header assignments without charging any scalar arithmetic to a
mathematical evaluator. Each expression is executed using the RAM's unit address operations. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

open Block Tape Polynomial

abbrev HeaderPlan (n : Nat) := List (Fin n × AddressTerm n)

namespace HeaderPlan
variable {n : Nat}

def output : HeaderPlan n → (Fin n → Nat) → (Fin n → Nat)
  | [], env => env
  | (dst,e)::rest, env => output rest (Function.update env dst (e.value env))

def cost : HeaderPlan n → (Fin n → Nat) → Nat
  | [], _ => 0
  | (dst,e)::rest, env => e.cost env + 1 + cost rest (Function.update env dst (e.value env))

def code (scratch : Nat) : HeaderPlan n → Block
  | [] => .skip
  | (dst,e)::rest => .seq (e.code scratch) (.seq (.op (.addrCopy dst scratch)) (code scratch rest))

/-- A uniform bound on the work of a fixed header plan when all of its arguments fit
within `B`. Composition bounds the effect of assignments on later expressions. -/
noncomputable def budget : HeaderPlan n → Polynomial Nat
  | [] => 0
  | (_,e)::rest => e.boundCost + 1 + (budget rest).comp (X + e.boundValue)

theorem cost_le (assigns : HeaderPlan n) (env : Fin n → Nat) (B : Nat) (h : ∀ i, env i ≤ B) :
    assigns.cost env ≤ assigns.budget.eval B := by
  induction assigns generalizing env B with
  | nil => simp [cost,budget]
  | cons head rest ih =>
    obtain ⟨dst,e⟩ := head
    let env' := Function.update env dst (e.value env)
    have henv' (i : Fin n) : env' i ≤ B+e.boundValue.eval B := by
      by_cases eq : i=dst
      · subst i; simpa [env'] using (e.value_le env B h).trans (Nat.le_add_left _ _)
      · simpa [env',eq] using (h i).trans (Nat.le_add_right _ _)
    simpa [cost,budget,Polynomial.eval_comp,env'] using
      Nat.add_le_add (Nat.add_le_add_right (e.cost_le env B h) 1) (ih env' _ henv')

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

/-- Execution updates exactly the specified low addresses and leaves the entire scalar
bank intact. Any scratch cells used by the compiler are counted in the actual trace. -/
theorem correct (assigns : HeaderPlan n) (scratch : Nat) (hscratch : n ≤ scratch)
    (s : Memory K) (env : Fin n → Nat) (henv : ∀ i : Fin n, s.index i = env i) (hs : Good P s) :
    ∃ t k, Eval (Good P) (code scratch assigns) s k t ∧ k ≤ assigns.cost env ∧ t.data = s.data ∧
      ∀ i : Fin n, t.index i = assigns.output env i := by
  induction assigns generalizing s env with
  | nil => exact ⟨s,0,.skip hs,le_rfl,rfl,henv⟩
  | cons head tail ih =>
    obtain ⟨d,e⟩ := head
    obtain ⟨k,u,comp,hk,ud,uf,uv⟩ := e.correct env scratch s hscratch henv hs
    let v := u.putIndex d (u.index scratch)
    have cp : Eval (Good P) (.op (.addrCopy d scratch)) u 1 v := eval_copyI u comp.safe_end _ _
    let env' := Function.update env d (e.value env)
    have hv (i : Fin n) : v.index i = env' i := by
      by_cases eq : i=d
      · subst i; simp [v,env',uv]
      · have neq : i.val ≠ d.val := fun hh => eq (Fin.ext hh)
        simpa [v,env',eq,neq] using (uf i (i.isLt.trans_le hscratch)).trans (henv i)
    obtain ⟨t,l,rest,hl,td,ti⟩ := ih v env' hv cp.safe_end
    refine ⟨t,k+(1+l),comp.seq (cp.seq rest),?_,td.trans ud,ti⟩
    change k+(1+l) ≤ e.cost env+1+cost tail env'
    omega

end HeaderPlan
end Call
end RAM
end LinearProgramming
end Optimization
end OAI
