import OAI.Computability.NearSquareRoot.PrecisionGridQuantization
import OAI.Computability.NearSquareRoot.PrecisionGrid

/-! # Finite table entries for the phase-slot accuracy requirement -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductRecovery

open FixedPoint IntegerMultiplication

/-- A unit phase admits a finite signed table entry at the standard precision.
The witness is an actual P192 record. This existence lemma imposes no running
time bound on the generation of the rational sample. -/
theorem exists_phase_record (k : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ c : Record k, ‖value k c - z‖ ≤ 1/(2:ℝ)^(70*k) := by
  let p := fractionBits k
  let δ := 1/(2:ℝ)^(p+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨a, ha, ha'⟩ := exists_rat_btwn (show z.re - δ < z.re by linarith)
  obtain ⟨b, hb, hb'⟩ := exists_rat_btwn (show z.im - δ < z.im by linarith)
  have hδ' : δ + δ = 1/(2:ℝ)^p := by unfold δ; rw [pow_succ]; ring
  have he : ‖complexRat a b - z‖ ≤ 1/(2:ℝ)^p := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    change |(a : ℝ) - z.re| + |(b : ℝ) - z.im| ≤ _
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith), ← hδ']
    linarith
  have hpow : 1 ≤ (2:ℝ)^p := one_le_pow₀ (by norm_num)
  have hn : ‖complexRat a b‖ ≤ 2 := by
    have h := norm_le_norm_sub_add (complexRat a b) z
    rw [hz] at h
    linarith [one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hpow]
  have hw : p+2 ≤ componentBits k := by unfold p fractionBits componentBits; omega
  have fits : ‖complexRat a b‖ * (2:ℝ)^p + 1/2 < 2^(componentBits k) := by
    have large := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hw
    rw [pow_add] at large
    norm_num at large
    nlinarith [mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ (2:ℝ)^p)]
  refine ⟨quantize p _ a b, ?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub _ (complexRat a b) _).trans (by
    have err := quantize_error fits
    change ‖Grid.meaning p (componentBits k) (quantize p _ a b) - complexRat a b‖ +
      ‖complexRat a b - z‖ ≤ _
    calc
      _ ≤ 1/(2:ℝ)^p + 1/(2:ℝ)^p := add_le_add err he
      _ = _ := by unfold p fractionBits; rw [pow_succ]; ring)

end ProductRecovery

end NearSquareRoot
end Computability
end OAI
