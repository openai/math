import OAI.LinearAlgebra.FiniteFourier.CircuitComposition
import OAI.LinearAlgebra.FiniteFourier.CircuitReindex
import OAI.LinearAlgebra.FiniteFourier.GeometricNewton

/-! # Circuit cost of a geometric factor from fixed convolution -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open ExactFourier.CoefficientTime Matrix
open scoped Matrix

variable {K : Type*} [Field K]

/-- Turning a lower triangular Toeplitz matrix upside-down gives its transpose. -/
theorem truncMatrix_transpose_reindex {K : Type*} [CommSemiring K] (a : ℕ) (f : PowerSeries K) :
    (truncMatrix a f)ᵀ = Matrix.reindex Fin.revPerm Fin.revPerm (truncMatrix a f) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Fin.revPerm_symm, Fin.revPerm_apply, truncMatrix, Fin.val_rev]
  have hi := i.isLt
  have hj := j.isLt
  have hle : a - (j.val + 1) ≤ a - (i.val + 1) ↔ i.val ≤ j.val := by omega
  have hsub : a - (i.val + 1) - (a - (j.val + 1)) = j.val - i.val := by omega
  simp only [hle, hsub]

private theorem realizable_diagonal_free {a : ℕ} (v : Fin a → K) :
    RealizableAtMost (Matrix.diagonal v) 0 := by
  refine ⟨0, le_rfl, ⟨.nil, fun i ↦ .scaled (v i) (.inl i)⟩, ?_⟩
  ext i j
  by_cases hij : i = j <;>
    simp [Circuit.matrix, Circuit.eval, Readout.eval, hij]

/-- A uniform gate bound on triangular truncated convolutions also bounds the
allowed factors including upper triangular matrices. -/
theorem IsGridDiagonalOrToeplitz.realizable {a B : ℕ} {A : Matrix (Fin a) (Fin a) K}
    (h : IsGridDiagonalOrToeplitz A)
    (hconv : ∀ f : PowerSeries K, f.constantCoeff ≠ 0 → RealizableAtMost (truncMatrix a f) B) :
    RealizableAtMost A B := by
  cases h with
  | diagonal v _ =>
    obtain ⟨s, hs, hs'⟩ := realizable_diagonal_free v
    exact ⟨s, hs.trans (Nat.zero_le _), hs'⟩
  | lower f hf => exact hconv f hf
  | upper f hf => rw [truncMatrix_transpose_reindex]; exact (hconv f hf).reindex _ _

/-- Forward and inverse geometric factors have at most a constant multiple
of the triangular Toeplitz circuit cost. -/
theorem geometric_cost_of_convolution {a B : ℕ} (q : K) (hq : q ≠ 0)
    (hd : Function.Injective (fun i : Fin a ↦ q ^ i.val))
    (hconv : ∀ f : PowerSeries K, f.constantCoeff ≠ 0 → RealizableAtMost (truncMatrix a f) B)
    (A : Matrix (Fin a) (Fin a) K) (hA : A = geometricMatrix a q ∨ A = (geometricMatrix a q)⁻¹) :
    complexity A ≤ 7 * B := by
  obtain ⟨l, hl, hf, rfl⟩ := geometricMatrix_and_inverse_factors q hq hd A hA
  refine le_trans ?_ (Nat.mul_le_mul_right B hl)
  apply (complexity_le_iff ..).2
  clear hl hA
  induction l with
  | nil =>
    simpa [Matrix.diagonal_one] using (realizable_diagonal_free (fun _ : Fin a ↦ (1 : K)))
  | cons A l ih =>
    have h₁ := (hf A List.mem_cons_self).realizable hconv
    have h₂ := ih (fun C hC ↦ hf C (List.mem_cons_of_mem _ hC))
    simpa [Nat.succ_mul, Nat.add_comm] using h₁.mul h₂

end FiniteFourier
end LinearAlgebra
end OAI
