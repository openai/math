import OAI.Computability.NearSquareRoot.PrecisionChirpRoots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Guard bits for the normalized chirp sums

Each Bluestein multiplier and each restoration diagonal entry is one normalized
sum of at most `2 * a` phases. The integer accumulator adds the real and
imaginary numerators exactly before multiplying by one integer approximation
to the inverse square root. The error accounts for both input approximations
and a final rounding to the working grid.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChirpTable

open Finset

/-- Fractional working precision for a sum over a fiber of length `a`. -/
def sumPrecision (a target : ℕ) := target + Nat.clog 2 a + 5

/-- Error of a finite sum when each input phase is accurate to three units in
the last place, as supplied by `Star.direction`. -/
private theorem sum_error {ι : Type*} (s : Finset ι) (v f : ι → ℂ) (u : ℝ)
    (hv : ∀ i ∈ s, ‖v i - f i‖ ≤ 3*u) :
    ‖(∑ i ∈ s, v i) - ∑ i ∈ s, f i‖ ≤ s.card * (3*u) := by
  rw [← Finset.sum_sub_distrib]
  simpa using norm_sum_le_of_le s (fun i hi => hv i hi)

private theorem sum_norm {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ = 1) :
    ‖∑ i ∈ s, f i‖ ≤ s.card := by
  simpa using norm_sum_le_of_le s (fun i hi => (hf i hi).le)

/-- Guarded error budget for the two normalized short-transform tables.
`stored` is the accumulated output after a possible final rounding. -/
theorem normalized_sum_guarded {ι : Type*} (s : Finset ι) (ideal represented : ι → ℂ)
    (a target : ℕ) (ha : 0 < a) (hcard : s.card ≤ 2*a) (q : ℝ) (stored : ℂ)
    (hunit : ∀ i ∈ s, ‖ideal i‖ = 1)
    (hphase : ∀ i ∈ s, ‖represented i - ideal i‖ ≤ 3 / (2 : ℝ) ^ sumPrecision a target)
    (hscale : |q - (Real.sqrt a)⁻¹| ≤ 1 / (2 : ℝ) ^ sumPrecision a target)
    (hfinal : ‖stored - (q : ℂ) * ∑ i ∈ s, represented i‖ ≤ 2 / (2 : ℝ) ^ sumPrecision a target) :
    ‖stored - (Real.sqrt a : ℂ)⁻¹ * ∑ i ∈ s, ideal i‖ ≤ 1 / (2 : ℝ) ^ target := by
  let u := 1 / (2 : ℝ) ^ sumPrecision a target
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hs1 : 1 ≤ Real.sqrt a := Real.one_le_sqrt.mpr ha1
  have hs0 : 0 ≤ (Real.sqrt a)⁻¹ := by positivity
  have hs : (Real.sqrt a)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hq : ‖(q : ℂ)‖ ≤ 2 := by
    have e : |q - (Real.sqrt a)⁻¹| ≤ u := hscale
    rw [abs_le] at e
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hq' : ‖(q : ℂ) - (Real.sqrt a : ℂ)⁻¹‖ ≤ u := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hscale
  have hsum := sum_error s represented ideal u (fun i hi => by
    simpa [u, div_eq_mul_inv] using hphase i hi)
  have hf := sum_norm s ideal hunit
  have hn := (norm_sub_le_norm_sub_add_norm_sub stored
    ((q : ℂ) * ∑ i ∈ s, represented i) ((Real.sqrt a : ℂ)⁻¹ * ∑ i ∈ s, ideal i))
  have hm : (q : ℂ) * (∑ i ∈ s, represented i) - (Real.sqrt a : ℂ)⁻¹ * (∑ i ∈ s, ideal i) =
      q * ((∑ i ∈ s, represented i) - (∑ i ∈ s, ideal i)) +
      ((q : ℂ) - (Real.sqrt a : ℂ)⁻¹) * ∑ i ∈ s, ideal i := by ring
  rw [hm] at hn
  have hcost : ‖stored - (Real.sqrt a : ℂ)⁻¹ * ∑ i ∈ s, ideal i‖ ≤ (2 + 7*(s.card:ℝ))*u := by
    refine hn.trans ?_
    apply (add_le_add_right (norm_add_le _ _) _).trans
    rw [norm_mul, norm_mul]
    have hfinal' : ‖stored - (q : ℂ) * ∑ i ∈ s, represented i‖ ≤ 2*u := by
      simpa [u, div_eq_mul_inv] using hfinal
    nlinarith [mul_le_mul hq hsum (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      mul_le_mul hq' hf (norm_nonneg _) hu]
  apply hcost.trans
  have hclog : (a : ℝ) ≤ (2:ℝ) ^ Nat.clog 2 a := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) a
  have hc : (s.card : ℝ) ≤ 2*(a:ℝ) := by exact_mod_cast hcard
  dsimp [u, sumPrecision]
  rw [← div_eq_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
    pow_add, pow_add]
  nlinarith [mul_le_mul_of_nonneg_right
    (show (2:ℝ) + 7*s.card ≤ 2 ^ Nat.clog 2 a * 32 by linarith) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) target)]

/-- Displacement read on the `h`-th pass of the Bluestein kernel loop. -/
def displacement (a : ℕ) (h : Fin (2*a-1)) : ℤ := h.val + 1 - a

/-- Specialization to a row of the zero-extended Bluestein chirp. The coefficient
errors on the input side are exactly those returned by `Star.direction`. -/
theorem bluestein_guarded {a r : ℕ} (ha : 0 < a) (hr : 0 < r) (ξ target : ℕ)
    (represented : Fin (2*a-1) → ℂ) (q : ℝ) (stored : ℂ)
    (hphase : ∀ i, ‖represented i - IntegerMultiplication.Fourier.phase (2*a*r)
        (bluesteinIndex a r ξ (displacement a i) : ℤ)‖ ≤ 3 / (2:ℝ)^sumPrecision a target)
    (hscale : |q - (Real.sqrt a)⁻¹| ≤ 1 / (2 : ℝ) ^ sumPrecision a target)
    (hfinal : ‖stored - (q:ℂ) * ∑ i, represented i‖ ≤ 2 / (2 : ℝ) ^ sumPrecision a target) :
    ‖stored - Chirp.bluesteinMultiplier a ((ξ : ℝ) / r)‖ ≤ 1 / (2:ℝ)^target := by
  rw [bluestein_fin_sum ha hr]
  exact normalized_sum_guarded _ _ _ a target ha (by simp) _ _
    (fun _ _ => IntegerMultiplication.Fourier.phase_norm _ _) (fun i _ => hphase i) hscale hfinal

/-- Specialization to a row of the restoration diagonal, including the parity
correction at odd transform lengths. -/
theorem spectrum_guarded {a : ℕ} [NeZero a] (ξ : Fin a) (target : ℕ)
    (represented : Fin a → ℂ) (q : ℝ) (stored : ℂ)
    (hphase : ∀ i, ‖represented i - IntegerMultiplication.Fourier.phase (2*a)
        (spectrumIndex a ξ.val i.val : ℤ)‖ ≤ 3 / (2:ℝ)^sumPrecision a target)
    (hscale : |q - (Real.sqrt a)⁻¹| ≤ 1 / (2 : ℝ) ^ sumPrecision a target)
    (hfinal : ‖stored - (q:ℂ) * ∑ i, represented i‖ ≤ 2 / (2 : ℝ) ^ sumPrecision a target) :
    ‖stored - ShortFourier.chirpSpectrum a ξ‖ ≤ 1 / (2:ℝ)^target := by
  rw [spectrum_ordered_sum]
  exact normalized_sum_guarded _ _ _ a target (NeZero.pos a) (by simp; omega) _ _
    (fun _ _ => IntegerMultiplication.Fourier.phase_norm _ _) (fun i _ => hphase i) hscale hfinal

end ChirpTable

end NearSquareRoot
end Computability
end OAI
