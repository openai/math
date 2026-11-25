import OAI.Computability.NearSquareRoot.KernelPass
import Mathlib.Algebra.BigOperators.Fin

/-! # Exact execution of finite stream row banks

An input to a plan is an indexed bank of streams. Routing, forking and
combining banks preserve independent address coordinates. Only child
transforms contribute to the call count.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open Matrix Finset

abbrev Bank (A h i : ℕ) := Fin i → Addr A h → ℚ

namespace Plan

/-- Matrix action of a plan on a row bank. -/
def applyAt {A i o : ℕ} (p : Plan A i o) (h : ℕ) (x : Bank A h i) : Bank A h o :=
  Function.curry ((p.eval h).mulVec (Function.uncurry x))

theorem eval_eq_of_applyAt {A i o h : ℕ} {p : Plan A i o} {M : RowMatrix A h i o}
    (hp : ∀ x, p.applyAt h x = Function.curry (M.mulVec (Function.uncurry x))) :
    p.eval h = M := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  simpa only [applyAt, Function.uncurry_curry] using congrArg Function.uncurry (hp (Function.curry v))

theorem applyAt_seq {A i j o h} (p : Plan A j o) (q : Plan A i j) (x : Bank A h i) :
    (p.seq q).applyAt h x = p.applyAt h (q.applyAt h x) := by
  simp [applyAt, eval, Matrix.mulVec_mulVec]

theorem applyAt_mix {A i o h : ℕ} (c : Fin o → Fin i → Coefficient) (x : Bank A h i) :
    (Plan.mix c).applyAt h x = fun b y => ∑ a, value (c b a) * x a y := by
  funext b y
  simp [applyAt, eval, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

theorem applyAt_parallel {A i j o u h : ℕ} (p : Plan A i o) (q : Plan A j u)
    (x : Bank A h i) (y : Bank A h j) :
    (p.parallel q).applyAt h (Fin.append x y) = Fin.append (p.applyAt h x) (q.applyAt h y) := by
  funext b z
  refine Fin.addCases (fun l => ?_) (fun r => ?_) b <;>
    simp only [applyAt, eval, directSum, Function.curry_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Function.uncurry, Fin.append_left, Fin.append_right,
      Fin.addCases_left, Fin.addCases_right] <;>
    rw [Fin.sum_univ_add] <;> simp

/-- Routing, including copies and forgetting obsolete rows, is a fixed mix. -/
def route {A i o : ℕ} (r : Fin o → Fin i) : Plan A i o :=
  .mix fun b a => if a = r b then (1,0) else (0,0)

theorem applyAt_route {A i o h : ℕ} (r : Fin o → Fin i) (x : Bank A h i) :
    (route r).applyAt h x = x ∘ r := by
  rw [route, applyAt_mix]
  funext i a
  rw [Finset.sum_eq_single (r i)]
  · simp [value]
  · intro j _ hj
    simp [hj, value]
  · simp

@[simp] theorem calls_route {A i o : ℕ} (r : Fin o → Fin i) :
    (route (A := A) r).calls = 0 := rfl

/-- Execute both programs on independent copies of the same input. -/
def fork {A i o u : ℕ} (p : Plan A i o) (q : Plan A i u) : Plan A i (o+u) :=
  (p.parallel q).seq (route (Fin.append id id))

theorem applyAt_fork {A i o u h : ℕ} (p : Plan A i o) (q : Plan A i u) (x : Bank A h i) :
    (p.fork q).applyAt h x = Fin.append (p.applyAt h x) (q.applyAt h x) := by
  rw [fork, applyAt_seq, applyAt_route]
  have hx : x ∘ Fin.append (id : Fin i → Fin i) id = Fin.append x x := by
    funext a
    refine Fin.addCases (fun j => ?_) (fun j => ?_) a <;>
      simp only [Function.comp_apply, Fin.append_left, Fin.append_right, id_eq]
  rw [hx, applyAt_parallel]

@[simp] theorem calls_fork {A i o u : ℕ} (p : Plan A i o) (q : Plan A i u) :
    (p.fork q).calls = p.calls + q.calls := by simp [fork, calls]

/-- Apply one plan successively, without recomputing any intermediate bank. -/
def iterate {A i : ℕ} (p : Plan A i i) : ℕ → Plan A i i
  | 0 => route id
  | n+1 => p.seq (p.iterate n)

theorem applyAt_iterate {A i h : ℕ} (p : Plan A i i) (n : ℕ) (x : Bank A h i) :
    (p.iterate n).applyAt h x = (p.applyAt h)^[n] x := by
  induction n with
  | zero => simp [iterate, applyAt_route]
  | succ n ih => rw [iterate, applyAt_seq, ih, Function.iterate_succ_apply']

@[simp] theorem calls_iterate {A i : ℕ} (p : Plan A i i) (n : ℕ) :
    (p.iterate n).calls = n*p.calls := by
  induction n with
  | zero => simp [iterate]
  | succ n ih => simp [iterate, calls, ih, Nat.succ_mul, Nat.add_comm]

end Plan
end KernelPass

end NearSquareRoot
end Computability
end OAI
