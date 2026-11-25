import OAI.Computability.NearSquareRoot.KernelAutomatonAdd
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Serial composition of rational column transfer matrices

A transition in the composite sums over the middle address letter. The
Kronecker product retains each component's finite state. At a fixed width
the resulting series sums over entire middle addresses, as required for
ordinary matrix composition on a stream.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelAutomatonEquiv.Series

open Matrix
open scoped Matrix Kronecker

variable {O J I : Type*} [Fintype J]

/-- Output and input addresses read in parallel, most significant column first. -/
def columns {f : ℕ} (x : Fin f → O) (z : Fin f → I) : List (O × I) :=
  List.ofFn (fun c => (x c,z c))

private def productOn {S : Type*} [Fintype S] [DecidableEq S]
    (L : O × I → Matrix S S ℚ) {f : ℕ} (x : Fin f → O) (z : Fin f → I) :=
  ((columns x z).map L).prod

private theorem productOn_zero {S : Type*} [Fintype S] [DecidableEq S]
    (L : O × I → Matrix S S ℚ) (x : Fin 0 → O) (z : Fin 0 → I) :
    productOn L x z = 1 := rfl

private theorem productOn_succ {S : Type*} [Fintype S] [DecidableEq S]
    (L : O × I → Matrix S S ℚ) {f : ℕ} (x : Fin (f+1) → O) (z : Fin (f+1) → I) :
    productOn L x z = L (x 0,z 0) * productOn L (Fin.tail x) (Fin.tail z) := by
  unfold productOn columns
  rw [List.ofFn_succ, List.map_cons, List.prod_cons]
  rfl

/-- Per-column contraction over the middle letter. -/
def contract (A : Series (O × J)) (B : Series (J × I)) (xz : O × I) :
    Matrix (Fin A.dim × Fin B.dim) (Fin A.dim × Fin B.dim) ℚ :=
  ∑ j : J, A.letter (xz.1,j) ⊗ₖ B.letter (j,xz.2)

private theorem contract_product (A : Series (O × J)) (B : Series (J × I))
    {f : ℕ} (x : Fin f → O) (z : Fin f → I) :
    productOn (contract A B) x z =
      ∑ y : Fin f → J, productOn A.letter x y ⊗ₖ productOn B.letter y z := by
  classical
  induction f with
  | zero => simp [productOn_zero]
  | succ f ih =>
    rw [productOn_succ, ih, contract, Finset.sum_mul]
    simp_rw [Finset.mul_sum, ← Matrix.mul_kronecker_mul]
    let F (y : Fin (f+1) → J) := productOn A.letter x y ⊗ₖ productOn B.letter y z
    change _ = ∑ y, F y
    rw [← (Fin.consEquiv (fun _ : Fin (f+1) => J)).sum_comp F, Fintype.sum_prod_type]
    congr! 2 with j y
    dsimp [F]
    rw [productOn_succ A.letter, productOn_succ B.letter]
    rfl

private def tensorVec {S T : Type*} (u : S → ℚ) (v : T → ℚ) : S × T → ℚ :=
  fun q => u q.1 * v q.2

private theorem dot_tensor {S T : Type*} [Fintype S] [Fintype T]
    (u v : S → ℚ) (x y : T → ℚ) :
    tensorVec u x ⬝ᵥ tensorVec v y = (u ⬝ᵥ v) * (x ⬝ᵥ y) := by
  unfold dotProduct tensorVec
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  congr! 2 with i j
  ring

private theorem mulVec_tensor {S T : Type*} [Fintype S] [Fintype T]
    (P : Matrix S S ℚ) (Q : Matrix T T ℚ) (v : S → ℚ) (y : T → ℚ) :
    (P ⊗ₖ Q) *ᵥ tensorVec v y = tensorVec (P *ᵥ v) (Q *ᵥ y) := by
  funext ⟨i,j⟩
  exact dot_tensor (P i) v (Q j) y

/-- Serial composition as a finite weighted word automaton. -/
def compose (A : Series (O × J)) (B : Series (J × I)) : Series (O × I) :=
  ofEquiv finProdFinEquiv (tensorVec A.initial B.initial) (contract A B)
    (tensorVec A.final B.final)

/-- This transition construction gives exactly matrix multiplication on
the full width-f address space, with independent intermediate letters in
every column. -/
theorem eval_compose (A : Series (O × J)) (B : Series (J × I)) {f : ℕ}
    (x : Fin f → O) (z : Fin f → I) :
    (A.compose B).eval (columns x z) =
      ∑ y : Fin f → J, A.eval (columns x y) * B.eval (columns y z) := by
  classical
  rw [compose, ofEquiv_eval]
  change _ ⬝ᵥ (productOn (contract A B) x z *ᵥ _) = _
  rw [contract_product, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl (fun y _ => by rw [mulVec_tensor, dot_tensor]; rfl)

end KernelAutomatonEquiv.Series

end NearSquareRoot
end Computability
end OAI
