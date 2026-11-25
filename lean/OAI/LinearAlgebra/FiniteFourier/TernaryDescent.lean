import OAI.LinearAlgebra.FiniteFourier.TernaryPair
import OAI.LinearAlgebra.FiniteFourier.TernaryShearIsolation
import OAI.LinearAlgebra.FiniteFourier.GridFactor
import OAI.LinearAlgebra.FiniteFourier.WorkingLengths
import OAI.LinearAlgebra.FiniteFourier.ExtensionCircuit
import OAI.LinearAlgebra.FiniteFourier.PrimeKernel

/-! # Descending the ternary shear circuit in characteristic two

Over the ninth-root extension, a primitive ninth root supplies the parameters
for the twenty-eight-slot unit transvection. Pairing the binary axes and
expanding each extension register in a basis gives a uniform ground-field bound.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

universe u

/-- Descend a uniform ternary transform estimate at primitive cubic roots to
the binary shear tensor over a characteristic-two ground field. -/
theorem charTwo_shearTensorBound_of_kernel {c θ : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ)
    (hpow : ∀ (E : Type u) [Field E], (2 : E) = 0 → ∀ ζ : E, IsPrimitiveRoot ζ 3 →
      ∀ k : ℕ, (complexity (primeTransform 3 k ζ) : ℝ) ≤ c * 3^k * (1 + (k : ℝ))^θ)
    (K : Type u) [Field K] (h2 : (2 : K) = 0) :
    ShearTensorBound K θ (2 * 9^2 * (8 * 28 * c) + 9) := by
  intro j
  have h3 : (3 : K) ≠ 0 := by rw [show (3 : K) = 2+1 by norm_num, h2, zero_add]; exact one_ne_zero
  have h9 : (9 : K) ≠ 0 := by rw [show (9 : K) = 3^2 by norm_num]; exact pow_ne_zero _ h3
  let : NeZero ((9 : ℕ) : K) := ⟨by simpa using h9⟩
  let E := CyclotomicField 9 K
  let a := IsCyclotomicExtension.zeta 9 K E
  have ha : IsPrimitiveRoot a 9 := IsCyclotomicExtension.zeta_spec 9 K E
  let ζ := a^3
  have hζ : IsPrimitiveRoot ζ 3 := ha.pow (by decide) (by decide : 9 = 3 * 3)
  have hpoly : ζ^2 + ζ + 1 = 0 := by
    simpa [Finset.sum_range_succ, add_comm, add_assoc, add_left_comm] using hζ.geom_sum_eq_zero (by decide)
  have h2E : (2 : E) = 0 := by simpa only [map_ofNat, map_zero] using congrArg (algebraMap K E) h2
  have h3E : (3 : E) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap K E)).mpr h3
  obtain ⟨t, ht, hw⟩ := exists_ternaryFourierWord_unit_shear ζ a hpoly (isUnit_iff_ne_zero.mpr h3E)
    ha.pow_eq_one (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hζ.ne_one (by decide))))
  have hlocal := shearTensorBound_of_ternary_word hw hθ hc.le (hpow E h2E ζ hζ) j
  let : FiniteDimensional K E := (ha.powerBasis K).finite
  have hd : Module.finrank K E ≤ 9 := working_cyclotomic_finrank_le K
  have hdown := complexity_le_of_finiteExtension (E := E) (gridTensor (fun _ : Fin j => unitShear K))
  have hmap : (unitShear K).map (algebraMap K E) = unitShear E := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [unitShear]
  simp only [map_gridTensor, hmap, Fintype.card_fun, Fintype.card_fin] at hdown
  have hcost : (complexity (gridTensor (fun _ : Fin j => unitShear K)) : ℝ) ≤
      2 * 9^2 * (complexity (gridTensor (fun _ : Fin j => unitShear E)) : ℝ) + 9 * (2 : ℝ)^j := by
    exact_mod_cast hdown.trans (show _ ≤ 2 * 9^2 * _ + 9 * 2^j by gcongr)
  have hone : 1 ≤ (1 + (j : ℝ))^θ := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) j]) hθ
  calc
    _ ≤ 2 * 9^2 * ((8 * t * c) * (2 : ℝ)^j * (1 + (j : ℝ))^θ) + 9 * 2^j := by
      exact hcost.trans (by gcongr)
    _ ≤ 2 * 9^2 * ((8 * 28 * c) * (2 : ℝ)^j * (1 + (j : ℝ))^θ) +
        9 * 2^j * (1 + (j : ℝ))^θ := by
      apply add_le_add
      · gcongr
        exact_mod_cast ht
      · exact le_mul_of_one_le_right (by positivity) hone
    _ = _ := by ring

/-- A ternary prime-kernel template for characteristic two yields a uniform
bound on the binary unit-shear tensor over all fields of that characteristic. -/
theorem uniform_charTwo_shearTensorBound_of_batch {A W σ C : ℕ} {θ : ℝ}
    (hA : 0 < A) (hW : 0 < W) (hθ : 0 ≤ θ) (hs : (σ : ℝ) / W < (A : ℝ)^θ)
    (hbatch : ∀ (E : Type u) [Field E], (2 : E) = 0 → ∀ ζ : E, IsPrimitiveRoot ζ 3 →
      PrimeKernelBatch 3 A W σ C ζ) :
    ∃ D > (0 : ℝ), ∀ (K : Type u) [Field K], (2 : K) = 0 → ShearTensorBound K θ D := by
  obtain ⟨c, hc, hpow⟩ := uniform_primeTransform_bound_of_batch (C := C)
    (by decide : 1 < 3) hA hW hθ hs
  exact ⟨_, by positivity, charTwo_shearTensorBound_of_kernel hc hθ
    (fun E _ h2 ζ hζ k => by simpa using hpow E ζ (hbatch E h2 ζ hζ) k)⟩

end FiniteFourier
end LinearAlgebra
end OAI
