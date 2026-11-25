import OAI.Computability.NearSquareRoot.Asymptotic
import OAI.Computability.NearSquareRoot.InterchangeLogSlack
import OAI.Computability.NearSquareRoot.PrecisionDigitBounds
import OAI.Computability.NearSquareRoot.PrecisionWalshWidth

/-!
# From the padded-array budget to the input-length exponents

The array work is charged on all `N = 2^k` records and additive setup is
polynomial in `k`. The conversion uses the actual rounded digit counts and
address width. For each strictly larger exponent it absorbs every fixed
power of the extra `1 + log(2+k)` factor.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open DigitPacking Filter

/-- Full array charge with polylogarithmic per-record overhead and a separate
polynomial setup allowance. -/
noncomputable def integerBudget (C P ρ : ℝ) (l d n : ℕ) : ℝ :=
  let k := addressBits n
  C * ((capacity n : ℝ) * k) * (1 + (k:ℝ))^ρ * (1 + Real.log (2+k))^l +
    P * (1 + (k:ℝ))^d

/-- The range of exponents below `γ` absorbs all logarithmic factors in the
integer budget and the cost of computing the shape and other short data. -/
theorem eventually_integerBudget_le {C P ρ γ : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hρ : 0 ≤ ρ) (hργ : ρ < γ) (l d : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
      integerBudget C P ρ l d n ≤ K * n * logScale n ^ γ := by
  let A := 5 + (Real.log 2)⁻¹
  have ha : 0 < A := by dsimp [A]; positivity
  have ht : Tendsto (fun n => (2:ℝ) + addressBits n) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.comp addressBits_tendsto_atTop)
  have hslack := ht.eventually (eventually_logSlack 1 zero_le_one l hργ)
  have hset := addressBits_tendsto_atTop.eventually (eventually_polynomial_le_array_length P hP d)
  refine ⟨48 * (C * A^γ + 1), by positivity, ?_⟩
  filter_upwards [hslack, hset, eventually_ge_atTop (2:ℕ),
    addressBits_tendsto_atTop.eventually_ge_atTop 1] with n hover hsetup hn hk
  let k := addressBits n
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog := Real.log_nonneg hn'
  have hs : 1 ≤ logScale n := by unfold logScale; linarith
  have hs' : 1 ≤ logScale n ^ γ := Real.one_le_rpow hs (le_trans hρ hργ.le)
  have hx : 2 + (k:ℝ) ≤ A * logScale n := by
    have hu := (addressBits_log_bounds hn).2
    change (k:ℝ) ≤ _ at hu
    rw [div_eq_mul_inv] at hu
    unfold A logScale
    nlinarith [(inv_nonneg.mpr (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)))]
  have hlogk : 0 ≤ 1 + Real.log (2+(k:ℝ)) := by
    have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k] : 1 ≤ (2+k:ℝ))
    linarith
  have hex : (1+(k:ℝ))^ρ * (1+Real.log (2+k))^l ≤ A^γ * logScale n ^ γ := by
    calc
      _ ≤ (2+(k:ℝ))^ρ * (1+Real.log (2+k))^l := by gcongr; linarith
      _ ≤ (2+(k:ℝ))^γ := by simpa only [one_mul, mul_comm] using hover
      _ ≤ (A*logScale n)^γ := Real.rpow_le_rpow (by positivity) hx (le_trans hρ hργ.le)
      _ = _ := Real.mul_rpow ha.le (zero_le_one.trans hs)
  have hvol : (capacity n:ℝ) * k ≤ 48*(n:ℝ) := by exact_mod_cast (packed_volume hn).2
  have hcap : P * (1+(k:ℝ))^d ≤ (capacity n:ℝ) := by
    simpa only [capacity, Nat.cast_pow, Nat.cast_ofNat] using hsetup
  have hsetup' : P * (1+(k:ℝ))^d ≤ 48*(n:ℝ)*logScale n^γ := by
    calc
      _ ≤ (capacity n:ℝ) := hcap
      _ ≤ (capacity n:ℝ)*k :=
        le_mul_of_one_le_right (by positivity) (by exact_mod_cast hk)
      _ ≤ 48*(n:ℝ) := hvol
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hs'
  calc
    integerBudget C P ρ l d n =
      C*((capacity n:ℝ)*k)*((1+(k:ℝ))^ρ * (1+Real.log (2+k))^l) + P*(1+(k:ℝ))^d := by
        unfold integerBudget; ring
    _ ≤ C*(48*(n:ℝ))*(A^γ*logScale n^γ) + 48*(n:ℝ)*logScale n^γ := by gcongr
    _ = _ := by ring

/-- The budget can be instantiated with a different parameter and constants
for each requested exponent provided the worst-case step count `T` is fixed. -/
theorem allEpsilonBounds_of_integerBudget {T : ℕ → ℕ}
    (hT : ∀ ε : ℝ, 0 < ε → ∃ (ρ C P : ℝ) (l d : ℕ),
      0 ≤ ρ ∧ ρ < 1/2 + ε ∧ 0 ≤ C ∧ 0 ≤ P ∧
      ∀ᶠ n in atTop, (T n : ℝ) ≤ integerBudget C P ρ l d n) :
    AllEpsilonBounds T := by
  intro ε hε
  obtain ⟨ρ, C, P, l, d, hρ, hρε, hC, hP, h⟩ := hT ε hε
  obtain ⟨K, hK, h'⟩ := eventually_integerBudget_le hC hP hρ hρε l d
  exact ⟨K, hK, h.mp (h'.mono fun _ h₂ h₁ => h₁.trans h₂)⟩

end NearSquareRoot
end Computability
end OAI
