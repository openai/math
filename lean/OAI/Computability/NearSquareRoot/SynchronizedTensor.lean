import OAI.Computability.NearSquareRoot.SynchronizedConvolution
import OAI.Computability.NearSquareRoot.SynchronizedPadding

/-! # The synchronized padded transform realizes residue-box convolution

The individual cyclic matrices have normalization `1/√aᵢ`. Their tensor consequently has
normalization `1/√S`, where `S` counts the valid addresses. The conjugate transpose
of the padded tensor gives the correctly normalized negative-sign transform on valid inputs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ResidueFourier

open Matrix Finset SynchronizedPadding
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} [∀ i, NeZero (a i)]

/-- The single cyclic axis transform, in the positive-sign convention. -/
def axisMatrix (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun k j => (Real.sqrt n : ℂ)⁻¹ * ZMod.stdAddChar (j * k)

theorem star_stdAddChar {n : ℕ} [NeZero n] (t : ZMod n) :
    star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  simp only [ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle t)).symm

theorem axisMatrix_unitary (n : ℕ) [NeZero n] : (axisMatrix n)ᴴ * axisMatrix n = 1 := by
  classical
  have hsq : (Real.sqrt n : ℂ)^2 = n := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
  have hreal : star (Real.sqrt n : ℂ) = (Real.sqrt n : ℂ) := by simp
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, axisMatrix, Matrix.of_apply,
    star_mul', star_inv₀, hreal, star_stdAddChar, Matrix.one_apply]
  have rearrange (k : ZMod n) :
      (Real.sqrt n : ℂ)⁻¹ * ZMod.stdAddChar (-(i * k)) *
        ((Real.sqrt n : ℂ)⁻¹ * ZMod.stdAddChar (j * k)) =
      ((Real.sqrt n : ℂ)^2)⁻¹ * ZMod.stdAddChar ((j-i)*k) := by
    rw [sub_mul, sub_eq_neg_add, AddChar.map_add_eq_mul, pow_two, _root_.mul_inv_rev]
    ring
  simp_rw [rearrange]
  rw [← mul_sum]
  by_cases hij : i = j
  · subst j
    simp [hsq, NeZero.ne (n : ℂ)]
  · have hj : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
    rw [show (∑ k : ZMod n, ZMod.stdAddChar ((j - i) * k)) = 0 from
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar _ hj)]
    simp [hij]

private theorem prod_sqrt : (∏ i, (Real.sqrt (a i) : ℂ)) = scale a := by
  unfold scale
  simp only [Box, Fintype.card_pi, ZMod.card, Nat.cast_prod]
  rw [Real.sqrt_prod univ (fun i _ => Nat.cast_nonneg (a i)), Complex.ofReal_prod]

theorem tensorMatrix_axisMatrix_apply (x y : Box a) :
    tensorMatrix (fun i => axisMatrix (a i)) x y = (scale a)⁻¹ * phase y x := by
  simp [tensorMatrix, axisMatrix, phase, prod_mul_distrib, prod_inv_distrib, prod_sqrt]

theorem tensorMatrix_forward (f : Box a → ℂ) :
    tensorMatrix (fun i => axisMatrix (a i)) *ᵥ f = forward f := by
  funext k
  simp [Matrix.mulVec, dotProduct, tensorMatrix_axisMatrix_apply, forward, transform,
    mul_assoc, mul_sum]

theorem tensorMatrix_adjoint (f : Box a → ℂ) :
    (tensorMatrix (fun i => axisMatrix (a i)))ᴴ *ᵥ f = adjoint f := by
  funext x
  have h (k : Box a) : star (phase x k) = phase (-x) k := by
    simp [phase, star_prod, star_stdAddChar]
  simp only [Matrix.mulVec, dotProduct, conjTranspose_apply, tensorMatrix_axisMatrix_apply,
    star_mul', star_inv₀, h]
  have hs : star (scale a) = scale a := by simp [scale]
  simp [adjoint, hs, mul_sum, mul_assoc]

/-- The exact three-transform computation on the full padded array yields the
digit convolution on the valid addresses, with every unused address zero. -/
theorem padded_recover (b : ι → ℕ) (f g : Box a → ℂ) :
    let P := tensorMatrix (fun i => axisPadding (b := Fin (b i)) (axisMatrix (a i)))
    let extend := zeroExtend (fun i => Fin (b i)) (R := ℂ) (A := fun i => ZMod (a i))
    (fun x => scale a * (Pᴴ *ᵥ ((P *ᵥ extend f) * (P *ᵥ extend g))) x) =
      extend (convolution f g) := by
  dsimp only
  rw [paddedSpectralProduct, tensorMatrix_forward, tensorMatrix_forward, tensorMatrix_adjoint]
  funext y
  by_cases hy : y ∈ Set.range (occupied (A := fun i => ZMod (a i)) (fun i => Fin (b i)))
  · obtain ⟨x, rfl⟩ := hy
    simp only [zeroExtend_occupied]
    exact recover_convolution f g x
  · simp [zeroExtend_off _ _ hy]

end
end ResidueFourier

end NearSquareRoot
end Computability
end OAI
