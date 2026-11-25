import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.TagFinite
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagOptimized
import OAI.LinearAlgebra.TensorSpectrum.TagEntropy

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

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

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass

theorem Character.shared_tag_optimized_of_pos (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {s : ℕ} (hs : 0 < s) (A : Fin s → Tensor O X Y Z)
    (hA : ∀ i, 0 < (f (ofTensor (A i)) : ℝ)) (hp : 0 < f.pX) :
    (∑ i, (f (ofTensor (A i)) : ℝ) ^ (1 / f.pX)) ^ f.pX ≤
      (f (ofTensor (Separation.shared A)) : ℝ) := by
  apply Integral.tag_optimized_of_fiber_bounds hs f.pX hp
    (fun i => (f (ofTensor (A i)) : ℝ)) hA
    (f (ofTensor (Separation.shared A)) : ℝ)
    (f (ofTensor (Separation.shared A))).coe_nonneg
  intro N hN c hc
  exact f.tag_count_fiber A c hc

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass
