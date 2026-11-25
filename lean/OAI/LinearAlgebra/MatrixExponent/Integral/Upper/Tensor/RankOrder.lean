import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Semiring
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Rank

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# Rank bounds and the concrete tensor order

Natural numbers in the quotient semiring are precisely the diagonal tensors.
These lemmas connect ordinary finite decompositions to the order used by states.
-/

open OAI.MatrixMultiplication.Foundation
open OAI.LinearAlgebra.MatrixExponent.Integral.Upper.CoefficientTensor

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass

theorem ofTensor_zero {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] :
    ofTensor (0 : Tensor O X Y Z) = 0 := by
  change ofTensor (0 : Tensor O X Y Z) = ofTensor emptyTensor
  apply ofTensor_eq
  · refine ⟨fun x => x.elim, fun y => y.elim, fun z => z.elim, ?_⟩
    funext x
    exact x.elim
  · refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
    funext x y z
    simp [Tensor.restrict]

theorem natCast_eq_ofTensor_natTensor (n : ℕ) :
    (n : TensorClass) = ofTensor (natTensor n) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, ofTensor_natTensor_zero]
    exact ofTensor_zero.symm
  | succ n ih =>
    rw [Nat.cast_succ, ih, ofTensor_natTensor_add n 1, ← ofTensor_add,
      ofTensor_natTensor_one]
    rfl

theorem rank_add_le (A B : TensorClass) : rank (A + B) ≤ rank A + rank B := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      change rank (ofRep a + ofRep b) ≤ rank (ofRep a) + rank (ofRep b)
      rw [← ofTensor_coeff a, ← ofTensor_coeff b, ofTensor_add]
      simp only [rank_ofTensor]
      exact CoefficientTensor.rank_blockSum_le _ _

theorem rank_mul_le (A B : TensorClass) : rank (A * B) ≤ rank A * rank B := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      change rank (ofRep a * ofRep b) ≤ rank (ofRep a) * rank (ofRep b)
      rw [← ofTensor_coeff a, ← ofTensor_coeff b, ofTensor_mul]
      simp only [rank_ofTensor]
      exact CoefficientTensor.rank_product_le _ _

theorem le_rank_natCast (A : TensorClass) : A ≤ (rank A : TensorClass) := by
  induction A using Quotient.inductionOn with | h a =>
    change ofRep a ≤ (rank (ofRep a) : TensorClass)
    rw [← ofTensor_coeff a, rank_ofTensor, natCast_eq_ofTensor_natTensor]
    exact ofTensor_le ((rankAtMost_iff_natTensor_restricts _ _).mp
      (CoefficientTensor.rank_spec a.coeff))

theorem rank_eq_zero_iff (A : TensorClass) : rank A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hle := le_rank_natCast A
    rw [h, Nat.cast_zero] at hle
    exact le_antisymm hle (zero_le A)
  · rintro rfl
    change rank (ofTensor emptyTensor) = 0
    rw [rank_ofTensor, CoefficientTensor.rank_eq_zero_iff]
    funext x
    exact x.elim

theorem mul_le_rank_mul (z x : TensorClass) : z * x ≤ (rank x : TensorClass) * z := by
  rw [mul_comm (rank x : TensorClass) z]
  exact mul_mono (le_refl z) (le_rank_natCast x)

@[simp] theorem Character.map_natCast (f : Character) (n : ℕ) : f n = n :=
  _root_.map_natCast f.toHom n

theorem Character.le_rank (f : Character) (A : TensorClass) : f A ≤ rank A := by
  have h := f.monotone' (le_rank_natCast A)
  simpa only [Character.map_natCast] using h

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass
