import OAI.Computability.BorderVNP.TeamScales
import OAI.Computability.VPVNP.CompressionBudget

/-! # Charged cables after repeated shortening

Proposition 7.2 divides the cost in (6.1) by the number of original copies represented by a
pack. The maximum normalized potential then halves at each epoch up to an additive term
proportional to the initial site count. The resulting bound is uniform in the batch size,
even when that size grows as a stretched exponential in the processor length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open Filter TeamScales

/-- Iterating the per-original-copy version of (6.1). -/
theorem normalized_potential_le (I : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A) (T : ℕ)
    (step : ∀ j < T, I (j + 1) ≤ I j / 2 + A) :
    I T ≤ I 0 / 2 ^ T + 2 * A := by
  induction T with
  | zero => simp; linarith
  | succ T ih =>
    have hj := ih (fun j h => step j (by omega))
    calc
      _ ≤ I T / 2 + A := step T (by omega)
      _ ≤ (I 0 / 2 ^ T + 2 * A) / 2 + A := by linarith
      _ = _ := by rw [pow_succ]; ring

/-- A positive gap between exponents absorbs constants even when the target power is rounded
to an integral processor width. -/
theorem eventually_le_rounded_width {a b ε : ℝ} (hab : a < b) (hb : 0 < b) (hε : 0 < ε)
    (A : ℝ) : ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ a ≤ ε * width n b := by
  have hgap := VPVNP.Compression.eventually_absorb_polylog A 0 hab
    (show 0 < ε / 2 by positivity)
  have hbig := ((tendsto_rpow_atTop hb).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  filter_upwards [hgap, hbig] with n hn hn'
  simp only [pow_zero, mul_one] at hn
  have hf := Nat.lt_floor_add_one ((n : ℝ) ^ b)
  change _ < (width n b : ℝ) + 1 at hf
  change 2 ≤ (n : ℝ) ^ b at hn'
  exact hn.trans (by nlinarith [mul_nonneg hε.le (show 0 ≤ 2 * (width n b : ℝ) - (n : ℝ)^b by linarith)])

/-- The charged width per original copy is little-o of the exterior budget in (7.2).
The integer epoch count is rounded down and the exterior capacity is rounded down before it is
multiplied by the number of processors. `A` bounds the initial routing overhead and `B`
includes the fixed multiple of the initial site count. -/
theorem eventually_charged_width {τ : ℝ} (hτ : 0 < τ) (hτ' : τ < 1 / 2) (D : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ (A B ε : ℝ), 0 ≤ A → 0 ≤ B → 0 < ε →
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2 ^ ((n : ℝ) ^ ω) →
    ∀ I : ℕ → ℝ,
      I 0 ≤ A * volume τ r n * (logWidth r n : ℝ) ^ D →
      (∀ j < epochs τ n, I (j + 1) ≤ I j / 2 + B * r * (n : ℝ) ^ (9 / 10 : ℝ)) →
      I (epochs τ n) ≤ ε * exterior (τ / 5) r n := by
  obtain ⟨ω, hω, hlog⟩ := exists_polylog_budget D (show 0 < τ / 2000 by positivity)
  refine ⟨ω, hω, ?_⟩
  intro A B ε hA hB hε
  have hex : 0 < 1 - τ / 5 := by linarith
  have hpart := eventually_le_rounded_width
    (show (1 + τ / 20 + τ / 2000) + (-τ) < 1 - τ / 5 by linarith) hex
    (show 0 < ε / 2 by positivity) (2 * A)
  have hsites := eventually_le_rounded_width (show 9 / 10 < 1 - τ / 5 by linarith) hex
    (show 0 < ε / 2 by positivity) (2 * B)
  filter_upwards [hlog, hpart, hsites, eventually_ge_atTop 1] with n hl h1 h2 hn
  intro r hr hr' I hstart hstep
  have hp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcharged : I 0 / (2 : ℝ) ^ epochs τ n ≤ (r : ℝ) * (ε / 2 * width n (1 - τ / 5)) := by
    calc
      _ = I 0 * (1 / (2 : ℝ) ^ epochs τ n) := by ring
      _ ≤ (A * (r * (n : ℝ) ^ (1 + τ / 20)) * (n : ℝ) ^ (τ / 2000)) *
          (2 * (n : ℝ) ^ (-τ)) := by
        apply mul_le_mul _ (VPVNP.Compression.inv_two_pow_blockCount τ hn) (by positivity)
          (by positivity)
        exact hstart.trans (mul_le_mul_of_nonneg_left (hl r hr hr') (by unfold volume; positivity))
      _ = (r : ℝ) * ((2 * A) * (n : ℝ) ^ ((1 + τ / 20 + τ / 2000) + (-τ))) := by
        rw [Real.rpow_add hp (1 + τ / 20 + τ / 2000) (-τ), Real.rpow_add hp (1 + τ / 20) (τ / 2000)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hsum := (normalized_potential_le I (by positivity) (epochs τ n) hstep).trans
    (add_le_add hcharged le_rfl)
  have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (r : ℝ) by positivity)
  simp only [exterior, Nat.cast_mul]
  linarith only [hsum, h2']

end Packing

end BorderVNP
end Computability
end OAI
