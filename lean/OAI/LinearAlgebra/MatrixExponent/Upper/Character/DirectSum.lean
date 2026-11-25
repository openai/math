import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.Powers

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

/-!
# Character values of full direct sums

Every summand has independent coordinates on all three legs.  This file does
not apply additivity to a tensor whose first leg is shared.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass

private def headTailProduct (n : ℕ) (X : Type*) :
    (Fin (n + 1) × X) ≃ X ⊕ (Fin n × X) where
  toFun p := Fin.cases (Sum.inl p.2) (fun i => Sum.inr (i, p.2)) p.1
  invFun
    | .inl x => (0, x)
    | .inr p => (p.1.succ, p.2)
  left_inv p := by
    rcases p with ⟨i, x⟩
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    rcases p with x | ⟨i, x⟩ <;> rfl

theorem ofTensor_directSum_fin {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (n : ℕ)
    (A : Fin n → Tensor Coeff X Y Z) :
    ofTensor (Tensor.directSum A) = ∑ i, ofTensor (A i) := by
  classical
  induction n with
  | zero =>
    have hzero : Tensor.directSum A = 0 := by
      funext x
      exact Fin.elim0 x.1
    rw [hzero, ofTensor_zero]
    simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, ← ih (fun i => A i.succ), ofTensor_add]
    have heq : Tensor.pullback (headTailProduct n X) (headTailProduct n Y)
        (headTailProduct n Z)
        (CoefficientTensor.blockSum (A 0) (Tensor.directSum (fun i => A i.succ))) =
        Tensor.directSum A := by
      funext x y z
      rcases x with ⟨i, x⟩
      rcases y with ⟨j, y⟩
      rcases z with ⟨k, z⟩
      refine Fin.cases ?_ (fun i => ?_) i <;>
        refine Fin.cases ?_ (fun j => ?_) j <;>
        refine Fin.cases ?_ (fun k => ?_) k <;>
        simp [Tensor.pullback, headTailProduct, CoefficientTensor.blockSum,
          Tensor.directSum, eq_comm]
    rw [← heq]
    exact ofTensor_pullback_equiv _ _ _ _

theorem Character.map_directSum_fin (f : Character) {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (n : ℕ)
    (A : Fin n → Tensor Coeff X Y Z) :
    f (ofTensor (Tensor.directSum A)) = ∑ i, f (ofTensor (A i)) := by
  rw [ofTensor_directSum_fin]
  exact map_sum f.toHom _ _

end OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass
