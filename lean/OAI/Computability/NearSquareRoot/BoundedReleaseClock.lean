import OAI.Computability.NearSquareRoot.Asymptotic

/-! # Cost of releasing a fixed-tape multiplication program

The compiler, input loader and output scan have a combined clock bounded by a
constant times the sum of the internal program clock, the input width and one.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open Filter

/-- A nonnegative logarithmic exponent absorbs the linear tape-interface cost
without using any slack in the exponent. -/
theorem affine_io_eventually {T : ℕ → ℕ} {ρ C : ℝ} (hρ : 0 ≤ ρ)
    (hC : 0 < C) (h : ∀ᶠ n in atTop, (T n : ℝ) ≤ C * n * logScale n ^ ρ) (K : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n in atTop,
      ((K * (T n + n + 1) : ℕ) : ℝ) ≤ D * n * logScale n ^ ρ := by
  refine ⟨((K : ℝ) + 1) * (C + 2), by positivity, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℕ), tendsto_logScale.eventually_ge_atTop 1]
    with n hT hn hlog
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hscale := Real.one_le_rpow hlog hρ
  have hlinear : (n : ℝ) ≤ n * logScale n ^ ρ :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hscale
  push_cast
  calc
    (K : ℝ) * ((T n : ℝ) + n + 1)
      ≤ ((K : ℝ) + 1) * ((C + 2) * n * logScale n ^ ρ) := by
        apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
        linarith
    _ = _ := by ring

/-- The same program clock can be released once while retaining every
fixed-exponent bound for that machine. -/
theorem AllEpsilonBounds.affine_io {T : ℕ → ℕ} (h : AllEpsilonBounds T) (K : ℕ) :
    AllEpsilonBounds (fun n => K * (T n + n + 1)) := by
  intro ε hε
  obtain ⟨C, hC, bound⟩ := h ε hε
  exact affine_io_eventually (by linarith) hC bound K

end NearSquareRoot
end Computability
end OAI
