import OAI.Computability.NearSquareRoot.KernelPassRectBank

/-! # Finite sums and dyadic scalar multiples of restricted plans -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Rect

open Matrix Finset
open scoped BigOperators

variable {A i o : ℕ} {I O K : Type} [Fintype I] [Fintype O] [Fintype K]

def emptyPlan : Plan A i o := .mix fun _ _ => (0,0)

@[simp] theorem calls_emptyPlan : (emptyPlan (A := A) (i := i) (o := o)).calls = 0 := rfl

@[simp] theorem eval_emptyPlan (h : ℕ) : (emptyPlan (A := A) (i := i) (o := o)).eval h = 0 := by
  ext b a
  simp [emptyPlan, Plan.eval, value]

def addPlan (p q : Plan A i o) : Plan A i o :=
  (Plan.mix (fun b => Fin.append (fun a => if b = a then (1,0) else (0,0))
    (fun a => if b = a then (1,0) else (0,0)))).seq (p.fork q)

theorem eval_addPlan (p q : Plan A i o) (h : ℕ) : (addPlan p q).eval h = p.eval h + q.eval h := by
  apply Plan.eval_eq_of_applyAt
  intro x
  funext b y
  rw [addPlan, Plan.applyAt_seq, Plan.applyAt_mix, Plan.applyAt_fork, Matrix.add_mulVec]
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have pick (b : Prop) [Decidable b] : value (if b then (1,0) else (0,0)) = if b then 1 else 0 := by
    split <;> simp [value]
  simp [pick, ite_mul, Plan.applyAt]

@[simp] theorem calls_addPlan (p q : Plan A i o) : (addPlan p q).calls = p.calls + q.calls := by
  simp [addPlan, Plan.calls]

def totalList (ps : List (Plan A i o)) : Plan A i o := ps.foldr addPlan emptyPlan

theorem eval_totalList (ps : List (Plan A i o)) (h : ℕ) :
    (totalList ps).eval h = (ps.map (Plan.eval h)).sum := by
  induction ps with
  | nil => simp [totalList]
  | cons p ps ih => exact (eval_addPlan p (totalList ps) h).trans (by simp [ih])

theorem calls_totalList (ps : List (Plan A i o)) :
    (totalList ps).calls = (ps.map Plan.calls).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact (calls_addPlan p (totalList ps)).trans (by simp [ih])

noncomputable def total (p : K → Plan A i o) : Plan A i o :=
  totalList (List.ofFn (p ∘ (Fintype.equivFin K).symm))

theorem eval_total (p : K → Plan A i o) (h : ℕ) : (total p).eval h = ∑ k, (p k).eval h := by
  simp only [total, eval_totalList, List.map_ofFn, List.sum_ofFn]
  exact (Fintype.equivFin K).symm.sum_comp (fun k => (p k).eval h)

theorem calls_total (p : K → Plan A i o) : (total p).calls = ∑ k, (p k).calls := by
  simp only [total, calls_totalList, List.map_ofFn, List.sum_ofFn]
  exact (Fintype.equivFin K).symm.sum_comp (fun k => (p k).calls)

theorem block_total (p : K → On A I O) (h : ℕ) :
    block (O := O) (I := I) (total p) h = ∑ k, block (I := I) (O := O) (p k) h := by
  ext b a y x
  simp only [block, eval_total, Matrix.sum_apply]

def times (c : Coefficient) (p : Plan A 1 1) : Plan A 1 1 := (Plan.mix fun _ _ => c).seq p

@[simp] theorem calls_times (c : Coefficient) (p : Plan A 1 1) : (times c p).calls = p.calls := by
  simp [times, Plan.calls]

theorem matrix_times (c : Coefficient) (p : Plan A 1 1) (h : ℕ) :
    oneRow ((times c p).eval h) = value c • oneRow (p.eval h) := by
  ext y x
  classical
  change (∑ k : Fin 1 × Addr A h, (if k.2 = y then value c else 0) * p.eval h k (0,x)) = _
  simp [Fintype.sum_prod_type, ite_mul, oneRow]

end KernelPass.Rect

end NearSquareRoot
end Computability
end OAI
