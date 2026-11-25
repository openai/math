import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Character.TagFinite
import OAI.LinearAlgebra.TensorSpectrum.TagOptimized
import OAI.LinearAlgebra.TensorSpectrum.TagEntropy

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

/-!
# Optimized tagging for actual tensor characters

The finite count-fiber premise is discharged by the actual tensor restriction
and charged separation construction.  Only then is the polynomial number of
fibers removed.  No multinomial asymptotics or uncharged auxiliary tensor is
used.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass

theorem Character.shared_tag_optimized_of_pos (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {s : ℕ} (hs : 0 < s) (A : Fin s → Tensor Coeff X Y Z)
    (hA : ∀ i, 0 < (f (ofTensor (A i)) : ℝ)) (hp : 0 < f.pX) :
    (∑ i, (f (ofTensor (A i)) : ℝ) ^ (1 / f.pX)) ^ f.pX ≤
      (f (ofTensor (Separation.shared A)) : ℝ) := by
  apply TensorSpectrum.tag_optimized_of_fiber_bounds hs f.pX hp
    (fun i => (f (ofTensor (A i)) : ℝ)) hA
    (f (ofTensor (Separation.shared A)) : ℝ)
    (f (ofTensor (Separation.shared A))).coe_nonneg
  intro N hN c hc
  exact f.tag_count_fiber A c hc

theorem Character.shared_tag_optimized (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {s : ℕ} (hs : 0 < s) (A : Fin s → Tensor Coeff X Y Z)
    (hA : ∀ i, A i ≠ 0) (hp : 0 < f.pX) :
    (∑ i, (f (ofTensor (A i)) : ℝ) ^ (1 / f.pX)) ^ f.pX ≤
      (f (ofTensor (Separation.shared A)) : ℝ) := by
  apply f.shared_tag_optimized_of_pos hs A (fun i => ?_) hp
  have h := f.one_le_of_tensor_ne_zero (A i) (hA i)
  have hr : (1 : ℝ) ≤ f (ofTensor (A i)) := by exact_mod_cast h
  linarith

/-- The full tag inequality, including zero probabilities and a vanishing
dot-product exponent.  The two limiting steps have already been completed in
the polynomial degeneration and finite-word proofs, respectively. -/
theorem Character.shared_tag_entropy (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {s : ℕ} (hs : 0 < s) (A : Fin s → Tensor Coeff X Y Z)
    (hA : ∀ i, 0 < (f (ofTensor (A i)) : ℝ))
    (q : Fin s → ℝ) (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) :
    Real.exp (f.pX * (-(∑ i, q i * Real.log (q i)))) *
        (∏ i, (f (ofTensor (A i)) : ℝ) ^ q i) ≤
      (f (ofTensor (Separation.shared A)) : ℝ) := by
  by_cases hp : f.pX = 0
  · rw [hp]
    apply TensorSpectrum.tag_entropy_exp_zero_le
      (fun i => (f (ofTensor (A i)) : ℝ)) q
      (f (ofTensor (Separation.shared A)) : ℝ) hA hq hqsum
    intro i
    exact_mod_cast f.shared_branch_le A i
  · have hp' : 0 < f.pX := lt_of_le_of_ne f.pX_nonneg (Ne.symm hp)
    exact TensorSpectrum.tag_entropy_exp_le_of_bound f.pX
      (f (ofTensor (Separation.shared A)) : ℝ)
      (fun i => (f (ofTensor (A i)) : ℝ)) q hp' hA hq hqsum
      (f.shared_tag_optimized_of_pos hs A hA hp')

end OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass
