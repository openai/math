import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Dense indexing of intermediate block states

An ordered product with fixed endpoints has one free state at each internal
boundary. The left and right operand of a factor are consecutive reads of the
same tuple. Other per-block private choices can be summed independently.
-/

namespace ThreeFlat.Diagonal

open scoped BigOperators

theorem prod_entry_boundary {F S : Type*} [CommSemiring F] [Fintype S] [DecidableEq S]
    (n : ℕ) (K : Fin (n+1) → Matrix S S F) (x y : S) :
    (List.ofFn K).prod x y = ∑ v : Fin n → S, ∏ i : Fin (n+1),
      K i (Fin.cons (α := fun _ => S) x v i) (Fin.snoc (α := fun _ => S) v y i) := by
  classical
  induction n generalizing x with
  | zero =>
    simp [List.ofFn_succ]
    simp [Fin.snoc]
  | succ n ih =>
    let along (v : Fin (n+1) → S) := ∏ i : Fin (n+2), K i (Fin.cons (α := fun _ => S) x v i) (Fin.snoc (α := fun _ => S) v y i)
    change _ = ∑ v, along v
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => S)).sum_comp along, Fintype.sum_prod_type,
      List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro z _
    rw [ih _ z, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [along, Fin.consEquiv, Equiv.coe_fn_mk, ← Fin.cons_snoc_eq_snoc_cons]
    conv_rhs => rw [Fin.prod_univ_succ]
    simp

/-- Entry expansion for a block with a private interior choice at each time. -/
theorem prod_entry_private {F S A : Type*} [CommSemiring F] [Fintype S] [DecidableEq S] [Fintype A]
    (n : ℕ) (K : Fin (n+1) → A → Matrix S S F) (x y : S) :
    (List.ofFn fun i => ∑ z : A, K i z).prod x y =
      ∑ v : Fin n → S, ∑ h : Fin (n+1) → A, ∏ i : Fin (n+1),
        K i (h i) (Fin.cons (α := fun _ => S) x v i) (Fin.snoc (α := fun _ => S) v y i) := by
  classical
  rw [prod_entry_boundary]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Matrix.sum_apply, Fintype.prod_sum]

end ThreeFlat.Diagonal

end OAI
