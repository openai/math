import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Choosing one auxiliary output per tick

A choice of `n` words specifies the successive auxiliary outputs. Each
tick reads the previous output; the input to the first tick is supplied
separately. The endpoint test occurs only at the end of the block.
-/

namespace ThreeFlat.Diagonal

variable {F A : Type*} [Semiring F] [Fintype A] [DecidableEq A]

/-- The weight along a fixed auxiliary trajectory. -/
def auxPathWeight : (n : ℕ) → (Fin n → Matrix A A F) → A → (Fin n → A) → A → F
  | 0, _, a, _, b => if a = b then 1 else 0
  | n + 1, K, a, v, b =>
      K 0 a (v 0) * auxPathWeight n (fun i => K i.succ) (v 0) (fun i => v i.succ) b

/-- Product of tick entries before the projection onto the final auxiliary word. -/
def auxProduct : (n : ℕ) → (Fin n → Matrix A A F) → A → (Fin n → A) → F
  | 0, _, _, _ => 1
  | n + 1, K, a, v =>
      K 0 a (v 0) * auxProduct n (fun i => K i.succ) (v 0) (fun i => v i.succ)

/-- Last output on a chosen auxiliary trajectory. -/
def endWord {B : Type*} : (n : ℕ) → B → (Fin n → B) → B
  | 0, a, _ => a
  | n + 1, _, v => endWord n (v 0) (fun i => v i.succ)

omit [Fintype A] in
theorem auxPathWeight_eq (n : ℕ) (K : Fin n → Matrix A A F) (a b : A) (v : Fin n → A) :
    auxPathWeight n K a v b =
      if endWord n a v = b then auxProduct n K a v else 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    by_cases h : endWord n (v 0) (fun i => v i.succ) = b <;>
      simp [auxPathWeight, endWord, auxProduct, ih, h]

/-- Matrix composition sums the weights of exactly those auxiliary
trajectories ending at the prescribed word. -/
theorem sum_auxPathWeight (n : ℕ) (K : Fin n → Matrix A A F) (a b : A) :
    ∑ v : Fin n → A, auxPathWeight n K a v b = (List.ofFn K).prod a b := by
  classical
  induction n generalizing a with
  | zero => simp [auxPathWeight, Matrix.one_apply]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A)).sum_comp
      (fun v => auxPathWeight (n + 1) K a v b), Fintype.sum_prod_type,
      List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro m _
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, auxPathWeight, Fin.cons_zero, Fin.cons_succ,
      ← Finset.mul_sum, ih]

end ThreeFlat.Diagonal

end OAI
