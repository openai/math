import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Degeneration
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.DirectSum
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Separation

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

/-!
# The charged separation inequality for actual characters

The output is evaluated using full direct-sum additivity.  Exactly `6*M`
source copies are paid for, and the auxiliary dot product is retained.  In
the equal-value case the number of output blocks cancels the factor `M` in
that source cost, but never the auxiliary dot-product factor.
-/

noncomputable section

open scoped BigOperators NNReal
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass

theorem Character.charged_separation (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {M : ℕ} (hM : 0 < M) (A : Fin M → Tensor O X Y Z) :
    (∑ h, f (ofTensor (A h))) *
        f (ofTensor (Separation.dotPairingX (Fin M))) ≤
      (6 * M : ℝ≥0) * f (ofTensor (Separation.shared A)) := by
  obtain ⟨P, hconstant, hdegree, heval⟩ := Separation.finite_charged_separation hM A
  have h := f.polynomial_constant_le
    (Tensor.directSum (fun _ : Fin (6 * M) => Separation.shared A))
    (Separation.separated A) P ((M - 1) ^ 2) hconstant hdegree heval
  rw [Character.map_directSum_const] at h
  have houtput : f (ofTensor (Separation.separated A)) =
      (∑ h, f (ofTensor (A h))) *
        f (ofTensor (Separation.dotPairingX (Fin M))) := by
    unfold Separation.separated
    rw [Character.map_directSum_fin]
    simp only [← ofTensor_mul, Character.map_mul, Finset.sum_mul]
  rw [houtput] at h
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

/-- The block count pays the growing part of the separation cost.  The
remaining factor six is fixed, and is removed only in a later power limit. -/
theorem Character.charged_separation_equal (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {M : ℕ} (hM : 0 < M) (A : Fin M → Tensor O X Y Z)
    (c : ℝ≥0) (hvalue : ∀ h, f (ofTensor (A h)) = c) :
    c * f (ofTensor (Separation.dotPairingX (Fin M))) ≤
      6 * f (ofTensor (Separation.shared A)) := by
  have h := f.charged_separation hM A
  simp only [hvalue, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  have hM' : (0 : ℝ≥0) < M := by exact_mod_cast hM
  apply (mul_le_mul_iff_right₀ hM').mp
  calc
    (M : ℝ≥0) * (c * f (ofTensor (Separation.dotPairingX (Fin M)))) =
        ((M : ℝ≥0) * c) * f (ofTensor (Separation.dotPairingX (Fin M))) :=
      (mul_assoc _ _ _).symm
    _ ≤ (6 * M : ℝ≥0) * f (ofTensor (Separation.shared A)) := h
    _ = (M : ℝ≥0) * (6 * f (ofTensor (Separation.shared A))) := by ring

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass
