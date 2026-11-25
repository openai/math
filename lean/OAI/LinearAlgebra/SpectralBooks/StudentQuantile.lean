import OAI.LinearAlgebra.SpectralBooks.StudentTail
import OAI.LinearAlgebra.SpectralBooks.GaussianTest

namespace OAI
/-!
# Quantile inversion for a square multiplication tensor

At square weights the three terms in the Student test coincide. Inverting
the tail at one third gives the finite-dimensional exponent bound.
-/

noncomputable section

open Set MeasureTheory

namespace LinearAlgebra.SpectralBooks

/-- The generalized inverse of the Student CDF with `d` degrees of freedom. -/
def studentQuantile (d : ℕ) (p : ℝ) : ℝ :=
  sInf {s : ℝ | p ≤ 1 - studentTail d s}

theorem studentTail_zero {d : ℕ} (hd : 0 < d) : studentTail d 0 = 1 / 2 := by
  simp only [studentTail, zero_div, zero_mul, normalTail_zero, integral_mul_const, integral_chiDensity hd,
    one_mul]

theorem studentTail_antitone {d : ℕ} (hd : 0 < d) : Antitone (studentTail d) := by
  intro a b hab
  apply integral_mono (integrable_chiDensity_mul_normalTail hd _) (integrable_chiDensity_mul_normalTail hd _)
  intro x
  by_cases hx : 0 < x
  · apply mul_le_mul_of_nonneg_left _ (chiDensity_nonneg hd x)
    refine measureReal_mono ?_ (measure_ne_top _ _)
    apply Ioi_subset_Ioi
    gcongr
  · simp [chiDensity, chiKernel, hx]

/-- Invert a Student tail bound at a quantile above the median. -/
theorem student_quantile_le_ratio {d : ℕ} (hd : 2 ≤ d) {p m L : ℝ}
    (hp : 1 / 2 < p) (hm : 0 < m) (hmL : m ≤ L)
    (h : studentTail d (Real.sqrt ((d : ℝ) * ((L / m) ^ (2 / ((d : ℝ) - 1)) - 1))) ≤ 1 - p) :
    (1 + (studentQuantile d p) ^ 2 / (d : ℝ)) ^ (((d : ℝ) - 1) / 2) ≤ L / m := by
  let z := Real.sqrt ((d : ℝ) * ((L / m) ^ (2 / ((d : ℝ) - 1)) - 1))
  let A := {x : ℝ | p ≤ 1 - studentTail d x}
  have hz : z ∈ A := by
    change p ≤ 1 - studentTail d z
    dsimp only [z]
    linarith
  have hA : 0 ∈ lowerBounds A := by
    intro x hx
    by_contra! hn
    have hx' : p ≤ 1 - studentTail d x := hx
    have hle := studentTail_antitone (by omega : 0 < d) hn.le
    rw [studentTail_zero (by omega)] at hle
    linarith
  have hq0 : 0 ≤ studentQuantile d p := le_csInf ⟨z, hz⟩ hA
  have hqz : studentQuantile d p ≤ z := csInf_le ⟨0, hA⟩ hz
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 1 := by linarith
  have hr : 1 ≤ L / m := (one_le_div hm).mpr hmL
  have hx := Real.one_le_rpow hr (by positivity : 0 ≤ 2 / ((d : ℝ) - 1))
  have hsq := Real.sq_sqrt (show 0 ≤ (d : ℝ) * ((L / m) ^ (2 / ((d : ℝ) - 1)) - 1)
    by positivity)
  have hs : (studentQuantile d p) ^ 2 ≤ z ^ 2 := by gcongr
  dsimp only [z] at hs
  rw [hsq] at hs
  have hb : 1 + studentQuantile d p ^ 2 / (d : ℝ) ≤ (L/m) ^ (2/((d : ℝ)-1)) := by
    rw [← le_sub_iff_add_le', div_le_iff₀ (by positivity : 0 < (d : ℝ))]
    linarith only [hs, mul_comm (d : ℝ) ((L/m)^(2/((d : ℝ)-1))-1)]
  calc
    _ ≤ ((L / m) ^ (2 / ((d : ℝ) - 1))) ^ (((d : ℝ) - 1) / 2) :=
      Real.rpow_le_rpow (by positivity) hb (by positivity)
    _ = L/m := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ L/m),
        show (2/((d : ℝ)-1)) * (((d : ℝ)-1)/2) = 1 by field_simp, Real.rpow_one]

/-- The three equal loads in the finite-dimensional square test give
`2 (1 + t²/d)^((d-1)/2) ≤ ω` for the two-thirds Student quantile `t`. -/
theorem student_square_lower_bound {d : ℕ} (hd : 2 ≤ d) {ω : ℝ} (hω : 2 ≤ ω)
    (h : 3 * studentTail d (Real.sqrt ((d : ℝ) * ((ω / 2) ^ (2 / ((d : ℝ) - 1)) - 1))) ≤ 1) :
    2 * (1 + (studentQuantile d (2 / 3)) ^ 2 / (d : ℝ)) ^ (((d : ℝ) - 1) / 2) ≤ ω := by
  have hq := student_quantile_le_ratio hd (p := 2 / 3) (by norm_num) (by norm_num) hω
    (by linarith)
  linarith

end LinearAlgebra.SpectralBooks

end
end OAI
