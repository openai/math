import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoEndpointSplit
import OAI.LinearAlgebra.FiniteFourier.OccupiedWord
import OAI.LinearAlgebra.FiniteFourier.GeometricMatrix

/-! # Frequency reversal over a commutative ring

For a unit-separated root of invertible order, the inverse Fourier transform
uses the forward word and a single normalized frequency permutation.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {R : Type*} [CommRing R] {b : ℕ}

theorem geometricMatrix_eq_dftMatrix (b : ℕ) (q : R) : geometricMatrix b q = dftMatrix b q := by
  ext i j
  exact geometricMatrix_apply b q i j

/-- The inverse Fourier matrix is a left inverse over a ring with unit-separated nodes. -/
theorem inverse_geometricMatrix_mul_of_separated (u : Rˣ) (hu : u ^ b = 1) (hb : IsUnit (b : R))
    (hs : Pairwise fun i j : Fin b => IsUnit ((u : R)^i.val - (u : R)^j.val)) :
    (geometricMatrix b (u : R))⁻¹ * geometricMatrix b (u : R) = 1 := by
  rw [geometricMatrix_eq_dftMatrix, Deformation.inv_dftMatrix_of_unit_differences u hu hb hs]
  exact Deformation.normalized_dftMatrix_mul_of_unit_differences u hu hb hs

/-- The normalized frequency permutation turns the forward matrix into its inverse. -/
theorem exists_monomial_mul_geometricMatrix_inverse [NeZero b] (u : Rˣ) (hu : u ^ b = 1)
    (hb : IsUnit (b : R))
    (hs : Pairwise fun i j : Fin b => IsUnit ((u : R)^i.val - (u : R)^j.val)) :
    ∃ P, LayerMatrix .monomial P ∧ P * geometricMatrix b (u : R) =
      (geometricMatrix b (u : R))⁻¹ := by
  let P : Matrix (Fin b) (Fin b) R := fun i j => if -i = j then (↑hb.unit⁻¹ : R) else 0
  have hP : LayerMatrix .monomial P := LayerMatrix.monomial (Equiv.neg _) (fun _ => hb.unit⁻¹)
  have hneg (i : Fin b) : u ^ (-i).val = u⁻¹ ^ i.val := by
    by_cases hi : i = 0
    · simp [hi]
    · have hi' : 0 < i.val := Nat.pos_of_ne_zero fun h => hi (Fin.ext (by simpa using h))
      have hval : (-i).val + i.val = b := by
        rw [Fin.val_neg', Nat.mod_eq_of_lt (by omega)]
        omega
      rw [inv_pow]
      apply eq_inv_of_mul_eq_one_left
      rwa [← pow_add, hval]
  have hPF : P * geometricMatrix b (u : R) = (geometricMatrix b (u : R))⁻¹ := by
    rw [geometricMatrix_eq_dftMatrix, Deformation.inv_dftMatrix_of_unit_differences u hu hb hs]
    ext i j
    rw [Matrix.mul_apply]
    simp only [P, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.smul_apply]
    change (↑hb.unit⁻¹ : R) * (u : R)^((-i).val * j.val) =
      (↑hb.unit⁻¹ : R) * (↑u⁻¹ : R)^(i.val * j.val)
    simp only [pow_mul, ← Units.val_pow_eq_pow_val, hneg]
  exact ⟨P, hP, hPF⟩

/-- Reversing the frequencies and scaling by the inverse order costs one monomial layer. -/
theorem layerWord_inverse_geometricMatrix_of_separated [NeZero b] {D : ℕ} (u : Rˣ)
    (hu : u ^ b = 1) (hb : IsUnit (b : R))
    (hs : Pairwise fun i j : Fin b => IsUnit ((u : R)^i.val - (u : R)^j.val))
    (hF : LayerWord D (geometricMatrix b (u : R))) :
    LayerWord (1 + D) (geometricMatrix b (u : R))⁻¹ := by
  obtain ⟨P, hP, heq⟩ := exists_monomial_mul_geometricMatrix_inverse u hu hb hs
  rw [← heq]
  exact layerWord_mul (layerWord_of_layer hP) hF

/-- Frequency reversal extends by the identity on all auxiliary registers. -/
theorem occupiedWord_inverse_geometricMatrix_of_separated [NeZero b] {W : Type}
    [Fintype W] [DecidableEq W] {D : ℕ} (u : Rˣ) (hu : u ^ b = 1) (hb : IsUnit (b : R))
    (hs : Pairwise fun i j : Fin b => IsUnit ((u : R)^i.val - (u : R)^j.val))
    (hF : OccupiedWord W D (geometricMatrix b (u : R))) :
    OccupiedWord W (1 + D) (geometricMatrix b (u : R))⁻¹ := by
  obtain ⟨P, hP, heq⟩ := exists_monomial_mul_geometricMatrix_inverse u hu hb hs
  rw [← heq]
  exact (layerWord_of_layer hP).occupied.mul hF

end FiniteFourier
end LinearAlgebra
end OAI
