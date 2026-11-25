import OAI.LinearAlgebra.FiniteFourier.IntegralTensorTheorem
import OAI.LinearAlgebra.FiniteFourier.PrimeKernelUniform
import OAI.LinearAlgebra.FiniteFourier.IntegralGridInputs

/-! # Applying the uniform prime kernels to integral tensors

The binary and ternary cyclotomic sums specialize to the protected eighth-
and ninth-root extensions. Their respective bounds may have different constants.
Taking every local factor equal to the binary shear yields the Fourier input.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

/-- Uniform prime Fourier estimates imply the integral estimate for every
bounded width, without any restriction on coefficients or ranks. -/
theorem boundedGridTensorEstimate_of_uniformKernels {β : ℝ} (hβ : 0 ≤ β)
    (hb : UniformPrimeKernelBound.{0} 2 β) (ht : UniformPrimeKernelBound.{0} 3 β)
    (d : ℕ) (hd : 2 ≤ d) : ∃ C > (0 : ℝ), BoundedGridTensorEstimate ℤ 2 d β C := by
  obtain ⟨B, hB, H₂⟩ := hb
  obtain ⟨T, hT, H₃⟩ := ht
  apply boundedGridTensorEstimate_of_protectedKernels hβ hB.le hT.le _ _ d hd
  · let E := ProtectedCyclotomic {2} 9
    let : IsDomain E := protectedCyclotomic_isDomain {2} 9 (by decide)
    let a : E := AdjoinRoot.root (cyclotomic 9 (protectedRationals {2}))
    have h3 : IsUnit (3 : E) := protectedCyclotomic_isUnit 9 (d := 3) (by decide) (by norm_num)
    have hζ : IsPrimitiveRoot (a^3) 3 := IsPrimitiveRoot.pow (by decide : 0 < 9)
      (protectedCyclotomic_primitive {2} 9 (by decide)) (by decide : 9 = 3*3)
    simpa using H₃ E (by simpa using h3) (a^3) (hζ.geom_sum_eq_zero (by decide))
  · intro L _ ho
    let E := ProtectedCyclotomic L 8
    have h2 : IsUnit (2 : E) := protectedCyclotomic_isUnit 8 (d := 2) (by decide)
      (fun l hl => Nat.coprime_two_right.mpr (ho l hl))
    simpa using H₂ E (by simpa using h2) (-1) (by norm_num [Finset.sum_range_succ])

/-- The tensor theorem on local width two computes the exact integral shear
used by the finite abelian Fourier upper bound. -/
theorem BoundedGridTensorEstimate.integralShearBound {β C : ℝ}
    (h : BoundedGridTensorEstimate ℤ 2 2 β C) : IntegralShearBound β C := by
  intro j
  let M := gridTensor (fun _ : Fin j => unitShear ℤ)
  obtain ⟨s, hs, p, hp⟩ := realizableAtMost_complexity M
  refine ⟨s, p, hp, (Nat.cast_le (α := ℝ) |>.mpr hs).trans ?_⟩
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    using h j (fun _ => 2) (fun _ => ⟨le_rfl, le_rfl⟩) (fun _ => unitShear ℤ)

/-- The two uniform prime-kernel estimates yield the integral shear bound
with its constant chosen before the tensor exponent. -/
theorem integralShearBound_of_uniformKernels {β : ℝ} (hβ : 0 ≤ β)
    (hb : UniformPrimeKernelBound.{0} 2 β) (ht : UniformPrimeKernelBound.{0} 3 β) :
    ∃ C > (0 : ℝ), IntegralShearBound β C := by
  obtain ⟨C, hC, H⟩ := boundedGridTensorEstimate_of_uniformKernels hβ hb ht 2 le_rfl
  exact ⟨C, hC, H.integralShearBound⟩

end FiniteFourier
end LinearAlgebra
end OAI
