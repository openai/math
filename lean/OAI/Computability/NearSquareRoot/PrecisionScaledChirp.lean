import OAI.Computability.NearSquareRoot.PrecisionPairRealization
import OAI.Computability.IntegerMultiplication.Grid.Value
import OAI.Computability.IntegerMultiplication.Fourier.Phase

/-! # Preparing the scaled chirp multiplier as a rational pair

The scalar compression factor is the imaginary part of the primitive root of
order 516. The normalized Bluestein sum and this one fixed-angle root can
both be passed as finite dyadic records.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Grid Strip Staff Carry Dusk Brief

/-- Exact rational coordinates carried by a finite dyadic record. -/
def grainRat (p : ℕ) {w : ℕ} (x : Grain w) : ℚ × ℚ :=
  ((Grid.aspect x).re / (2 : ℚ) ^ p, (Grid.aspect x).im / (2 : ℚ) ^ p)

theorem grainRat_value (p : ℕ) {w : ℕ} (x : Grain w) :
    toComplex (grainRat p x) = meaning p w x := by
  have h : (2 : ℂ) ^ p = (((2 : ℝ)^p : ℝ) : ℂ) := by push_cast; rfl
  rw [meaning, h]
  apply Complex.ext
  · rw [Complex.div_ofReal_re]; simp [grainRat, toComplex, toC]
  · rw [Complex.div_ofReal_im]; simp [grainRat, toComplex, toC]

theorem grainRat_realized {J : Type} {s : Regime J} {p w : J → ℕ} (P : Realizes s p)
    (x : (i : J) → Grain (w i)) (built : s.Has (fun i ↦ mark (x i))) :
    PairRealized s (fun i ↦ grainRat (p i) (x i)) := by
  let c (i : J) := Grid.disp (mark (x i))
  have C : s.Has c := built.ez Grid.disp_easy
  have re : Signed s (fun i ↦ (aspect (x i)).re) :=
    ⟨fun i ↦ (c i).1, C.ez Easy.fst, fun i ↦ congrArg QuadraticAlgebra.re (pullG (x i))⟩
  have im : Signed s (fun i ↦ (aspect (x i)).im) :=
    ⟨fun i ↦ (c i).2, C.ez Easy.snd, fun i ↦ congrArg QuadraticAlgebra.im (pullG (x i))⟩
  have ratio (f : J → ℤ) (hf : Signed s f) :
      RatRealized s (fun i ↦ (f i : ℚ) / 2 ^ p i) := by
    apply RatRealized.positiveDiv _ (RatRealized.powTwo p P) (fun _ ↦ by positivity)
    simpa only [RatRealized, Rat.cast_intCast] using Blot.integer hf
  exact ⟨ratio _ re, ratio _ im⟩

theorem phase516_im : (Fourier.phase 516 1).im = Real.sin (Real.pi / 258) := by
  unfold Fourier.phase Fourier.cis
  rw [Complex.exp_ofReal_mul_I_im]
  congr 1
  push_cast
  ring

/-- Exact rational scaling using the represented sine and the two components
of the represented normalized sum. -/
def scaleByImaginary (root coeff : ℚ × ℚ) : ℚ × ℚ :=
  (root.2 * coeff.1, root.2 * coeff.2)

theorem scaleByImaginary_realized {J : Type} {s : Regime J} {x y : J → ℚ × ℚ}
    (hx : PairRealized s x) (hy : PairRealized s y) :
    PairRealized s (fun j ↦ scaleByImaginary (x j) (y j)) :=
  ⟨RatRealized.mul hx.2 hy.1, RatRealized.mul hx.2 hy.2⟩

private theorem scaleByImaginary_value (x y : ℚ × ℚ) :
    toComplex (scaleByImaginary x y) = (((x.2 : ℝ) : ℂ)) * toComplex y := by
  apply Complex.ext <;> simp [toComplex, scaleByImaginary, Complex.mul_re, Complex.mul_im]

/-- Six guard bits absorb both errors, even for the largest bounded
Bluestein multiplier. -/
theorem scaleByImaginary_error (target : ℕ) (root coeff : ℚ × ℚ) (coeffExact : ℂ)
    (hCoeffNorm : ‖coeffExact‖ ≤ 40)
    (hcoeff : ‖toComplex coeff - coeffExact‖ ≤ 1 / (2 : ℝ) ^ (target + 6))
    (hroot : ‖toComplex root - Fourier.phase 516 1‖ ≤ 1 / (2 : ℝ) ^ (target + 6)) :
    ‖toComplex (scaleByImaginary root coeff) - Real.sin (Real.pi / 258) • coeffExact‖ ≤
      1 / (2 : ℝ) ^ target := by
  let σ := Real.sin (Real.pi / 258)
  let σ' : ℝ := root.2
  let u := 1 / (2 : ℝ) ^ (target + 6)
  have hu : u ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hσ : |σ' - σ| ≤ u := by
    have h := (Complex.abs_im_le_norm (toComplex root - Fourier.phase 516 1)).trans hroot
    simpa only [Complex.sub_im, phase516_im, toComplex, σ, σ', u] using h
  have hσ' : |σ'| ≤ 2 := by
    have h := abs_add_le (σ' - σ) σ
    rw [sub_add_cancel] at h
    linarith [Real.abs_sin_le_one (Real.pi / 258)]
  rw [scaleByImaginary_value, Complex.real_smul]
  change ‖(σ' : ℂ) * toComplex coeff - (σ : ℂ) * coeffExact‖ ≤ _
  calc
    _ = ‖(σ' : ℂ) * (toComplex coeff - coeffExact) + ((σ' - σ : ℝ) : ℂ) * coeffExact‖ := by
      congr 1; push_cast; ring
    _ ≤ ‖(σ' : ℂ) * (toComplex coeff - coeffExact)‖ + ‖((σ' - σ : ℝ) : ℂ) * coeffExact‖ := norm_add_le _ _
    _ ≤ 2 * u + u * 40 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul hσ' hcoeff (norm_nonneg _) (by norm_num))
        (mul_le_mul hσ hCoeffNorm (norm_nonneg _) (by dsimp [u]; positivity))
    _ ≤ _ := by
      unfold u
      rw [pow_add]
      field_simp
      norm_num

end PhaseTable

end NearSquareRoot
end Computability
end OAI
