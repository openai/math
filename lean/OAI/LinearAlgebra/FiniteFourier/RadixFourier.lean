import OAI.LinearAlgebra.FiniteFourier.GeometricMatrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Mixed-radix Fourier factorization

A Cooley–Tukey stage applies the smaller transforms on the two digit axes, with a
diagonal twiddle between the stages. The input packs the first digit at the low end,
and the output packs the second digit at the low end.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped Kronecker

/-- The input digit ordering of a mixed-radix stage. -/
def radixInputIndex (a b : ℕ) : Fin a × Fin b ≃ Fin (a * b) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm b a)))

private theorem radixPhase {K : Type*} [Monoid K] {q : K} {a b : ℕ}
    (h : q ^ (a * b) = 1) (u v w z : ℕ) :
    q ^ ((v + b * u) * (w + a * z)) =
      (q ^ b) ^ (u * w) * q ^ (v * w) * (q ^ a) ^ (v * z) := by
  rw [show (v + b * u) * (w + a * z) =
    (b * (u * w) + v * w + a * (v * z)) + (a * b) * (u * z) by ring,
    pow_add, pow_mul q (a * b), h, one_pow, mul_one, pow_add, pow_add,
    pow_mul q b, pow_mul q a]

/-- One Cooley–Tukey stage, including both digit permutations and the twiddle diagonal. -/
theorem geometricMatrix_radix {K : Type*} [CommRing K] (a b : ℕ) (q : K)
    (h : q ^ (a * b) = 1) :
    (geometricMatrix (a * b) q).submatrix finProdFinEquiv (radixInputIndex a b) =
      (geometricMatrix a (q ^ b) ⊗ₖ (1 : Matrix (Fin b) (Fin b) K)) *
      Matrix.diagonal (fun i : Fin a × Fin b => q ^ (i.1.val * i.2.val)) *
      ((1 : Matrix (Fin a) (Fin a) K) ⊗ₖ geometricMatrix b (q ^ a)) := by
  ext ⟨u, v⟩ ⟨w, z⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.mul_diagonal, Matrix.kronecker_apply, Matrix.one_apply,
    mul_ite, ite_mul, mul_zero, zero_mul, one_mul, mul_one]
  simp only [Matrix.submatrix_apply, geometricMatrix_apply]
  change q ^ ((v.val + b * u.val) * (w.val + a * z.val)) = _
  simpa [Nat.mul_comm w.val v.val] using radixPhase h u.val v.val w.val z.val

end FiniteFourier
end LinearAlgebra
end OAI
