import OAI.LinearAlgebra.FiniteFourier.OccupiedWord
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Extending a prime-orbit word by the scalar address -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Matrix

variable {R : Type*} {m : ℕ}

/-- Extend an orbit matrix by the identity at the distinguished address. -/
def dyadicPrimeOrbitBlock [Zero R] [One R] (A : Matrix (Fin m) (Fin m) R) :
    Matrix (Option (Fin m)) (Option (Fin m)) R
  | none, none => 1
  | some i, some j => A i j
  | _, _ => 0

/-- A protected scalar address does not change the depth or workspace of an orbit word. -/
theorem occupiedWord_dyadicPrimeOrbitBlock [CommSemiring R] {W : Type}
    [Fintype W] [DecidableEq W] {d : ℕ} {A : Matrix (Fin m) (Fin m) R}
    (h : OccupiedWord W d A) : OccupiedWord W d (dyadicPrimeOrbitBlock A) := by
  let split := (Equiv.optionEquivSumPUnit.{0} (Fin m)).trans (Equiv.sumComm _ _)
  let e := (split.sumCongr (Equiv.refl W)).trans (Equiv.sumAssoc _ _ _)
  have hp := (layerWord_parallel (layerWord_one (I := PUnit) d) h).relabel e.symm
  convert hp using 1
  ext (i | w) (j | v)
  · cases i <;> cases j <;> rfl
  · cases i <;> rfl
  · cases j <;> rfl
  · rfl

/-- Multiplication acts independently on the scalar and orbit blocks. -/
theorem dyadicPrimeOrbitBlock_mul [Semiring R] (A B : Matrix (Fin m) (Fin m) R) :
    dyadicPrimeOrbitBlock (A * B) = dyadicPrimeOrbitBlock A * dyadicPrimeOrbitBlock B := by
  ext i j
  cases i <;> cases j <;> simp [dyadicPrimeOrbitBlock, Matrix.mul_apply, Fintype.sum_option]

theorem dyadicPrimeOrbitBlock_one [Semiring R] :
    dyadicPrimeOrbitBlock (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [dyadicPrimeOrbitBlock, Matrix.one_apply]

/-- Inversion of an invertible orbit block fixes the distinguished address. -/
theorem dyadicPrimeOrbitBlock_inv [CommRing R] {A : Matrix (Fin m) (Fin m) R} (hA : IsUnit A) :
    (dyadicPrimeOrbitBlock A)⁻¹ = dyadicPrimeOrbitBlock A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← dyadicPrimeOrbitBlock_mul, A.mul_nonsing_inv (A.isUnit_iff_isUnit_det.mp hA),
    dyadicPrimeOrbitBlock_one]

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
