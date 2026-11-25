import OAI.LinearAlgebra.FiniteFourier.SemilocalBorderShear
import OAI.LinearAlgebra.FiniteFourier.BoundedEliminationInduction
import OAI.LinearAlgebra.FiniteFourier.BoundedEliminationContent
import OAI.LinearAlgebra.FiniteFourier.BoundedEliminationPivot

/-! # Bounded elimination over protected rationals

In each width-`n+1` block, two border shears create a generator pivot and two
more clear its row and column. Each border costs at most `n` transvections.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix Matrix.TransvectionStruct

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Clear the last row and column of a matrix around a unit pivot. -/
private theorem clear_unit_border (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R)
    (hu : IsUnit (M (.inr ()) (.inr ()))) :
    ∃ (b : Matrix (Fin n) Unit R) (c : Matrix Unit (Fin n) R),
      IsTwoBlockDiagonal (fromBlocks 1 b 0 1 * M * fromBlocks 1 0 c 1) := by
  obtain ⟨u, hu⟩ := hu
  let D : Matrix Unit Unit R := diagonal (fun _ => (u : R))
  have hd : M.toBlocks₂₂ = D := by
    ext ⟨⟩ ⟨⟩
    simpa [D, toBlocks₂₂] using hu.symm
  let b : Matrix (Fin n) Unit R := fun i _ => - M.toBlocks₁₂ i () * (↑(u⁻¹) : R)
  let c : Matrix Unit (Fin n) R := fun _ i => - (↑(u⁻¹) : R) * M.toBlocks₂₁ () i
  have hB : M.toBlocks₁₂ + b * D = 0 := by
    ext i ⟨⟩
    change M.toBlocks₁₂ i () + (b * D) i () = 0
    rw [Matrix.mul_apply]
    simp [D, b, mul_assoc]
  have hC : M.toBlocks₂₁ + D * c = 0 := by
    ext ⟨⟩ i
    change M.toBlocks₂₁ () i + (D * c) () i = 0
    rw [Matrix.mul_apply]
    simp [D, c, ← mul_assoc]
  refine ⟨b, c, ?_⟩
  rw [← fromBlocks_toBlocks M]
  simp [fromBlocks_multiply, hd, hB, hC, IsTwoBlockDiagonal]

variable [IsDomain R] [IsPrincipalIdealRing R] [Finite (MaximalSpectrum R)]

/-- Two border shears create a generator pivot; two further shears clear its border. -/
theorem exists_bounded_semilocal_block_step (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R) :
    ∃ L L' : List (TransvectionStruct (Fin n ⊕ Unit) R), L.length + L'.length ≤ 4 * n ∧
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod) := by
  classical
  by_cases hM : M = 0
  · exact ⟨[], [], by simp, by simp [hM]; exact ⟨rfl, rfl⟩⟩
  obtain ⟨d, N, hMN, hN⟩ := exists_primitive_matrix_part M hM
  obtain ⟨r, c, hrc⟩ := exists_semilocal_bilinear_unit_pivot N hN
  let A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R :=
    fromBlocks 1 0 (fun (_ : Unit) i => r i) 1
  let B : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R :=
    fromBlocks 1 (fun i (_ : Unit) => c i) 0 1
  obtain ⟨b', c', hbc⟩ := clear_unit_border (A * N * B) hrc
  obtain ⟨L₁, h₁, hA⟩ := exists_border_lower_transvections (fun (_ : Unit) i => r i)
  obtain ⟨L₂, h₂, hB⟩ := exists_border_upper_transvections (fun i (_ : Unit) => c i)
  obtain ⟨L₃, h₃, h₃'⟩ := exists_border_upper_transvections b'
  obtain ⟨L₄, h₄, h₄'⟩ := exists_border_lower_transvections c'
  refine ⟨L₃ ++ L₁, L₂ ++ L₄, by simp only [List.length_append]; omega, ?_⟩
  simp only [List.map_append, List.prod_append, hA, hB, h₃', h₄']
  rw [hMN, Matrix.mul_smul, Matrix.smul_mul]
  let C := fromBlocks 1 b' 0 1 * (A * N * B) * fromBlocks 1 0 c' 1
  have he : fromBlocks 1 b' 0 1 * A * N * (B * fromBlocks 1 0 c' 1) = C := by
    simp [C, Matrix.mul_assoc]
  change IsTwoBlockDiagonal (d • (fromBlocks 1 b' 0 1 * A * N * (B * fromBlocks 1 0 c' 1)))
  rw [he]
  change IsTwoBlockDiagonal C at hbc
  refine ⟨?_, ?_⟩
  · change d • C.toBlocks₁₂ = 0
    rw [hbc.1, smul_zero]
  · change d • C.toBlocks₂₁ = 0
    rw [hbc.2, smul_zero]

/-- Every matrix over a semilocal PID factors through a possibly singular diagonal
and two shear words of total length at most twice the square of the dimension. -/
theorem exists_semilocal_diagonal_shear_factorization {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I R) :
    ∃ (L L' : List (TransvectionStruct I R)) (D : I → R),
      L.length + L'.length ≤ 2 * (Fintype.card I) ^ 2 ∧
      M = (L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod :=
  exists_bounded_diagonal_shear_factorization_of_block_step
    (fun _ => exists_bounded_semilocal_block_step) M

/-- The bound over protected rationals is uniform in all entries and the protected primes. -/
theorem exists_protected_diagonal_shear_factorization {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (protectedRationals P)) :
    ∃ (L L' : List (TransvectionStruct I (protectedRationals P))) (D : I → protectedRationals P),
      L.length + L'.length ≤ 2 * (Fintype.card I) ^ 2 ∧
      M = (L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod := by
  let := isPrincipalIdealRing_protectedRationals P
  let := finite_maximalSpectrum_protectedRationals hP
  exact exists_semilocal_diagonal_shear_factorization M

end FiniteFourier
end LinearAlgebra
end OAI
