import OAI.Computability.NearSquareRoot.FixedCandidateArenaRelease
import OAI.Computability.NearSquareRoot.Asymptotic

/-! # Calibration of arithmetic files before choosing a physical digit split -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate
open Filter GeneratorSyntax

/-- For each reciprocal target exponent, one fixed calibration has both a fast
clock and linear storage. The index and resource constants are proof witnesses. -/
def Calibrated (T S : ℕ → ℕ → ℕ) : Prop :=
  ∀ j : ℕ, ∃ i : ℕ, ∃ H : ℝ, ∃ D : ℕ, 0 ≤ H ∧
    (∀ᶠ n : ℕ in atTop, (T i n : ℝ) ≤ H*n*logScale n^((1:ℝ)/2+1/(j+2:ℝ))) ∧
    ∀ᶠ n : ℕ in atTop, S i n ≤ D*(n+1)

/-- Shift all possible calibrations to positive template slots, leaving slot
zero available for any fixed fallback convention. -/
def ArenaFiles.positiveSlots {T S : ℕ → ℕ → ℕ} (f : ArenaFiles T S) :
    ArenaFiles (fun i => T i.pred) (fun i => S i.pred) where
  registers := f.registers
  positive := f.positive
  cmd := fun i => f.cmd i.pred
  effective := f.effective.comp Primrec.pred.to_comp
  bounded := fun i => f.bounded i.pred
  coeff := fun i => f.coeff i.pred
  body := fun i => f.body i.pred

/-- The physical digit machine spends a calibration-dependent fixed multiple
of its source time and area plus one linear scan. -/
theorem Calibrated.digit_bounds {T S : ℕ → ℕ → ℕ} (h : Calibrated T S) (E : ℕ → ℕ) (j : ℕ) :
    ∃ i : ℕ, ∃ H : ℝ, ∃ D : ℕ, 0 ≤ H ∧
      (∀ᶠ n : ℕ in atTop, ((E (i+1)*(T i n+n+1) : ℕ) : ℝ) ≤ H*n*logScale n^((1:ℝ)/2+1/(j+2:ℝ))) ∧
      ∀ᶠ n : ℕ in atTop, E (i+1)*(S i n+n+1) ≤ D*(n+1) := by
  obtain ⟨i,H,D,hH,ht,hs⟩ := h j
  let F := E (i+1)
  refine ⟨i,(F:ℝ)*(H+2),F*(D+1),by positivity,?_,?_⟩
  · filter_upwards [ht,eventually_ge_atTop (1:ℕ),tendsto_logScale.eventually_ge_atTop 1] with n hn hn' hl
    let w := logScale n^((1:ℝ)/2+1/(j+2:ℝ))
    have hw : 1 ≤ w := Real.one_le_rpow hl (by positivity)
    have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn'
    have grow := le_mul_of_one_le_right (Nat.cast_nonneg n (α := ℝ)) hw
    change (T i n : ℝ) ≤ H*n*w at hn
    change ((F*(T i n+n+1) : ℕ) : ℝ) ≤ F*(H+2)*n*w
    push_cast
    calc
      _ ≤ F*((H+2)*(n*w)) := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = _ := by ring
  · filter_upwards [hs] with n hn
    change F*(S i n+n+1) ≤ F*(D+1)*(n+1)
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
