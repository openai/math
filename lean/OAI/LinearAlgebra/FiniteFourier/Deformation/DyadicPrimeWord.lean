import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPrimeWordMatrix
import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPrimeWordMix
import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPrimeWordLift
import OAI.LinearAlgebra.FiniteFourier.DyadicFourierWord
import OAI.LinearAlgebra.FiniteFourier.AtTwoFourierInverse

/-! # Prime-axis words for the dyadic-list CRT

An arbitrary-order Fourier transform runs on the nonzero orbit with its original
occupied workspace. A diagonal and two row additions then convert to the scalar
and binomial basis. The inverse uses the factors in reverse order.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
namespace Deformation

open Matrix

variable {R : Type*} [CommRing R] {m : ℕ}

theorem dyadicPrimeForwardMatrix_factor (z : Fin m) (hz : z.val = 0)
    (u : Rˣ) (hm : IsUnit (m:R)) (hp : IsUnit ((m:R) + 1))
    (d : Fin m → Rˣ) (hd : (d z : R) = -1) :
    dyadicPrimeForwardMatrix z u hm d =
      dyadicPrimeMix z hm hp d * dyadicPrimeOrbitBlock (geometricMatrix m (u:R)) := by
  have hm' : (m:R) * (↑hm.unit⁻¹ : R) = 1 := by
    nth_rw 1 [← hm.unit_spec]
    exact hm.unit.mul_inv
  have hzero : -(((m:R)+1) * (↑hm.unit⁻¹ : R)) + 1 = -(↑hm.unit⁻¹ : R) := by
    linear_combination -hm'
  ext i j
  rw [dyadicPrimeMix, Matrix.mul_assoc, Matrix.mul_assoc]
  cases i with
  | none =>
    cases j <;> simp [dyadicPrimeForwardMatrix, dyadicPrimeScales, diagonal_mul,
      dyadicPrimeOrbitBlock, hz]
  | some i =>
    by_cases hi : i = z
    · subst i
      cases j <;> simp [dyadicPrimeForwardMatrix, dyadicPrimeScales, diagonal_mul,
        dyadicPrimeOrbitBlock, hz, hd, hzero]
    · cases j <;> simp [dyadicPrimeForwardMatrix, dyadicPrimeScales, diagonal_mul,
        dyadicPrimeOrbitBlock, hi]

/-- The forward and inverse prime-axis conversions incur seven additional slots
beyond the corresponding orbit Fourier word and reuse precisely its workspace. -/
theorem occupiedWord_dyadicPrimeForwardMatrix_pair {W : Type} [Fintype W] [DecidableEq W]
    {D : ℕ} (z : Fin m) (hz : z.val = 0) (u : Rˣ) (hm : IsUnit (m:R))
    (hp : IsUnit ((m:R) + 1)) (hu : u^m = 1)
    (hsep : Pairwise fun i j : Fin m => IsUnit ((u:R)^i.val - (u:R)^j.val))
    (d : Fin m → Rˣ) (hd : (d z : R) = -1)
    (hF : OccupiedWord W D (geometricMatrix m (u:R)))
    (hG : OccupiedWord W D (geometricMatrix m (u:R))⁻¹) :
    OccupiedWord W (7 + D) (dyadicPrimeForwardMatrix z u hm d) ∧
    OccupiedWord W (7 + D) (dyadicPrimeForwardMatrix z u hm d)⁻¹ := by
  rw [dyadicPrimeForwardMatrix_factor z hz u hm hp d hd]
  have hL := dyadicPrimeMix_layerWords z hm hp d
  refine ⟨hL.1.occupied.mul (occupiedWord_dyadicPrimeOrbitBlock hF), ?_⟩
  have hunit : IsUnit (geometricMatrix m (u:R)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse
      (inverse_geometricMatrix_mul_of_separated u hu hm hsep))
  rw [Matrix.mul_inv_rev, dyadicPrimeOrbitBlock_inv hunit, Nat.add_comm]
  exact (occupiedWord_dyadicPrimeOrbitBlock hG).mul hL.2.occupied

/-- Uniform protected words for either direction on a prime with orbit length
at most `B`, in the presence of the protected radix roots. -/
theorem protectedDyadicPrime_word_up_to {B r : ℕ}
    (hr : r = 2 ∨ r = 3) (hmB : m ≤ B)
    (hroots : ∀ j, r^j ≤ 8*B → IsUnit ((r^j : ℕ) : R) ∧ ∃ u : Rˣ, u^(r^j) = 1 ∧
      Pairwise fun i k : Fin (r^j) ↦ IsUnit ((u:R)^i.val - (u:R)^k.val))
    (hs : ∀ s : R, ∃ t : R, IsUnit t ∧ IsUnit (s-t))
    (z : Fin m) (hz : z.val = 0) (u : Rˣ) (hm : IsUnit (m:R)) (hp : IsUnit ((m:R) + 1))
    (hu : u^m = 1) (hsep : Pairwise fun i j : Fin m => IsUnit ((u:R)^i.val - (u:R)^j.val))
    (d : Fin m → Rˣ) (hd : (d z : R) = -1) :
    let F := dyadicPrimeForwardMatrix z u hm d
    let D := 7 + 6400 * (1 + Nat.clog 2 (2+B))
    OccupiedWord (Fin (13*m)) D F ∧ OccupiedWord (Fin (13*m)) D F⁻¹ := by
  apply occupiedWord_dyadicPrimeForwardMatrix_pair z hz u hm hp hu hsep d hd
  · exact protectedFourier_word_up_to hr (by omega) hmB hroots hs u.isUnit hsep (Or.inl rfl)
  · exact protectedFourier_word_up_to hr (by omega) hmB hroots hs u.isUnit hsep (Or.inr rfl)

end Deformation

end

end FiniteFourier
end LinearAlgebra
end OAI
