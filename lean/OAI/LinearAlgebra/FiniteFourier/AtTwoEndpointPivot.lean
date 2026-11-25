import OAI.LinearAlgebra.FiniteFourier.SemilocalPivot
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Semilocal pivot step for the endpoint basis changes

A unit pivot can be created by adding a linear combination of the other rows to the
last row. A Schur complement then leaves a smaller invertible matrix. In the
factorization, only two border rows, one border column and a unit scaling occur.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
open scoped Matrix

variable {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]

/-- Peel off one scalar pivot from an invertible matrix, using three border shears. -/
theorem semilocal_matrix_pivot {n : ℕ}
    (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R) (hM : IsUnit M) :
    ∃ (v : Matrix Unit (Fin n) R) (b : Matrix (Fin n) Unit R)
      (c : Matrix Unit (Fin n) R) (S : Matrix (Fin n) (Fin n) R) (s : Rˣ),
      IsUnit S ∧
      M = fromBlocks 1 0 v 1 * (fromBlocks 1 b 0 1 *
        fromBlocks S 0 0 (diagonal fun _ : Unit => (s : R)) * fromBlocks 1 0 c 1) := by
  classical
  let k : Fin n ⊕ Unit := .inr ()
  let x : Fin (n+1) → R := Fin.cons (M k k) (fun j => M (.inl j) k)
  let a : Fin (n+1) → R := Fin.cons (M⁻¹ k k) (fun j => M⁻¹ k (.inl j))
  have hax : ∑ i, a i * x i = 1 := by
    have hh := congrArg (fun A : Matrix _ _ R => A k k)
      (nonsing_inv_mul M ((isUnit_iff_isUnit_det M).mp hM))
    simpa [x, a, Fin.sum_univ_succ, mul_apply, Fintype.sum_sum_type, k, add_comm] using hh
  obtain ⟨d, hd⟩ := exists_semilocal_unit_pivot x a hax
  let V : Matrix Unit (Fin n) R := fun _ i => d i
  let L : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R := fromBlocks 1 0 V 1
  let P := L * M
  have hP : IsUnit P := by
    apply IsUnit.mul _ hM
    exact (isUnit_fromBlocks_zero₁₂ ..).mpr ⟨isUnit_one, isUnit_one⟩
  have he : P k k = M k k + ∑ i, d i * M (.inl i) k := by
    simp [k, P, L, V, fromBlocks, mul_apply, Fintype.sum_sum_type, add_comm]
  have hp : IsUnit (P k k) := by simpa [he, x] using hd
  have hD : IsUnit P.toBlocks₂₂ := by
    rw [isUnit_iff_isUnit_det, det_unique]
    exact hp
  let := hD.invertible
  have hf := fromBlocks_eq_of_invertible₂₂ P.toBlocks₁₁ P.toBlocks₁₂ P.toBlocks₂₁ P.toBlocks₂₂
  rw [fromBlocks_toBlocks] at hf
  have hs := isUnit_fromBlocks_iff_of_invertible₂₂.mp
    (show IsUnit (fromBlocks P.toBlocks₁₁ P.toBlocks₁₂ P.toBlocks₂₁ P.toBlocks₂₂) by
      rwa [fromBlocks_toBlocks])
  have hval : diagonal (fun _ : Unit => (hp.unit : R)) = P.toBlocks₂₂ := by
    ext i j
    cases i
    cases j
    simp [k, toBlocks₂₂]
  refine ⟨-V, P.toBlocks₁₂ * ⅟P.toBlocks₂₂, ⅟P.toBlocks₂₂ * P.toBlocks₂₁, _, hp.unit, hs, ?_⟩
  rw [hval, ← hf]
  dsimp only [P]
  rw [← Matrix.mul_assoc]
  simp [L, fromBlocks_multiply]

end FiniteFourier
end LinearAlgebra
end OAI
