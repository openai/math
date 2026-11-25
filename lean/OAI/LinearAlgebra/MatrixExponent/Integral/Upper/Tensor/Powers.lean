import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.RankOrder

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# Tensor powers and full repeated direct sums in the quotient

These bridges preserve the actual coefficient tensors used by interpolation.
-/

open scoped BigOperators NNReal
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass

private def finSuccFunctions (n : ℕ) (X : Type*) :
    (Fin (n + 1) → X) ≃ X × (Fin n → X) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    rcases p with ⟨x, f⟩
    rfl

theorem ofTensor_power {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor O X Y Z) (n : ℕ) :
    ofTensor (Tensor.power T n) = (ofTensor T) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    change ofTensor (Tensor.power T 0) = ofTensor unitTensor
    have heq : Tensor.pullback (Equiv.ofUnique (Fin 0 → X) PUnit)
        (Equiv.ofUnique (Fin 0 → Y) PUnit) (Equiv.ofUnique (Fin 0 → Z) PUnit)
        unitTensor = Tensor.power T 0 := by
      funext x y z
      simp [Tensor.pullback, Tensor.power, unitTensor]
    rw [← heq]
    exact ofTensor_pullback_equiv _ _ _ _
  | succ n ih =>
    rw [pow_succ', ← ih, ofTensor_mul]
    have heq : Tensor.pullback (finSuccFunctions n X) (finSuccFunctions n Y)
        (finSuccFunctions n Z) (Tensor.product T (Tensor.power T n)) =
        Tensor.power T (n + 1) := by
      funext x y z
      simp [Tensor.pullback, Tensor.product, Tensor.power, finSuccFunctions,
        Fin.prod_univ_succ]
    rw [← heq]
    exact ofTensor_pullback_equiv _ _ _ _

theorem ofTensor_directSum_const {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor O X Y Z) (n : ℕ) :
    ofTensor (Tensor.directSum (fun _ : Fin n => T)) =
      (n : TensorClass) * ofTensor T := by
  rw [natCast_eq_ofTensor_natTensor, ofTensor_mul]
  congr 1
  funext x y z
  simp only [Tensor.directSum, Tensor.product, CoefficientTensor.natTensor]
  split_ifs <;> simp

theorem Character.map_power_tensor (f : Character) {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor O X Y Z) (n : ℕ) :
    f (ofTensor (Tensor.power T n)) = (f (ofTensor T)) ^ n := by
  rw [ofTensor_power]
  exact f.toHom.map_pow _ _

theorem Character.map_directSum_const (f : Character) {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor O X Y Z) (n : ℕ) :
    f (ofTensor (Tensor.directSum (fun _ : Fin n => T))) =
      (n : ℝ≥0) * f (ofTensor T) := by
  rw [ofTensor_directSum_const, Character.map_mul, Character.map_natCast]

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass
