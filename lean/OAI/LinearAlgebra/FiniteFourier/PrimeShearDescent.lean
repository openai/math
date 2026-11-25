import OAI.LinearAlgebra.FiniteFourier.PrimeShear
import OAI.LinearAlgebra.FiniteFourier.ExtensionCircuit
import OAI.LinearAlgebra.FiniteFourier.WorkingLengths

/-! # Descending the four binary Fourier calls to odd characteristic

The eighth-root extension of a field of characteristic different from two
has degree at most eight. Expanding the registers in a basis therefore gives a
uniform reduction from the unit-shear tensor to the binary Fourier kernel.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

private theorem gridTensor_shear_map {K E : Type*} [Field K] [Field E] [Algebra K E] (j : ℕ) :
    (gridTensor (fun _ : Fin j => unitShear K)).map (algebraMap K E) =
      gridTensor (fun _ : Fin j => unitShear E) := by
  ext i k
  simp only [Matrix.map_apply, gridTensor, map_prod]
  apply Finset.prod_congr rfl
  intro q _
  generalize i q = a
  generalize k q = b
  fin_cases a <;> fin_cases b <;> simp [unitShear]

/-- A uniform simulation factor holds over every field in which two is nonzero,
without requiring the eighth roots of unity in the ground field. -/
theorem complexity_shear_le_binary_extension (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) (j : ℕ) :
    complexity (gridTensor (fun _ : Fin j => unitShear K)) ≤
      512 * complexity (primeTransform 2 j (-1 : CyclotomicField 8 K)) + 8 * 2 ^ j := by
  have h8 : (8 : K) ≠ 0 := by
    rw [show (8 : K) = 2^3 by norm_num]
    exact pow_ne_zero _ h2
  let : NeZero ((8 : ℕ) : K) := ⟨by simpa using h8⟩
  let E := CyclotomicField 8 K
  let x := IsCyclotomicExtension.zeta 8 K E
  have hx : IsPrimitiveRoot x 8 := IsCyclotomicExtension.zeta_spec 8 K E
  have hx₀ : x ≠ 0 := hx.ne_zero (by decide)
  have hx₄ : x^4 ≠ 1 := fun he => by
    have := hx.dvd_of_pow_eq_one _ he
    norm_num at this
  have h2E : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K E)).mpr h2
  have hword := complexity_shear_le_four_binary h2E hx₀ hx₄ j
  let : FiniteDimensional K E := (hx.powerBasis K).finite
  have hdown := complexity_le_of_finiteExtension (E := E) (gridTensor (fun _ : Fin j => unitShear K))
  rw [gridTensor_shear_map] at hdown
  have hd : Module.finrank K E ≤ 8 := working_cyclotomic_finrank_le K
  have hk : Fintype.card (Fin j → Fin 2) = 2 ^ j := by simp
  rw [hk] at hdown
  refine hdown.trans ?_
  calc
    _ ≤ 2 * 8 ^ 2 * (4 * complexity (primeTransform 2 j (-1 : E))) + 8 * 2 ^ j := by gcongr
    _ = _ := by ring

universe u

/-- A fixed binary template, valid after specialization in characteristic
different from two, implies the uniform shear tensor estimate throughout
those characteristics. The simulation constants do not depend on the field. -/
theorem uniform_odd_shearTensorBound_of_batch {A W σ C : ℕ} {θ : ℝ}
    (hA : 0 < A) (hW : 0 < W) (hθ : 0 ≤ θ) (hs : (σ : ℝ) / W < (A : ℝ)^θ)
    (hbatch : ∀ (E : Type u) [Field E], (2 : E) ≠ 0 → PrimeKernelBatch 2 A W σ C (-1 : E)) :
    ∃ D > (0 : ℝ), ∀ (K : Type u) [Field K], (2 : K) ≠ 0 → ShearTensorBound K θ D := by
  obtain ⟨c, hc, hpow⟩ := uniform_primeTransform_bound_of_batch (C := C)
    (by decide : 1 < 2) hA hW hθ hs
  refine ⟨512*c + 8, by positivity, fun K _ h2 j => ?_⟩
  let E := CyclotomicField 8 K
  have h2E : (2 : E) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap K E)).mpr h2
  have hcost := hpow E (-1) (hbatch E h2E) j
  have hdown := complexity_shear_le_binary_extension K h2 j
  have hd : (complexity (gridTensor (fun _ : Fin j => unitShear K)) : ℝ) ≤
      512 * (complexity (primeTransform 2 j (-1 : E)) : ℝ) + 8 * (2 : ℝ)^j := by exact_mod_cast hdown
  have hone : 1 ≤ (1 + (j : ℝ))^θ := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) j]) hθ
  push_cast at hcost
  nlinarith only [hd, hcost, mul_le_mul_of_nonneg_left hone (show 0 ≤ (2 : ℝ)^j by positivity)]

end FiniteFourier
end LinearAlgebra
end OAI
