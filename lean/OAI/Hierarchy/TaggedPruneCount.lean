import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace OAI
/-! # Absorbing the routing-selector entropy at wide payloads -/

noncomputable section
namespace Hierarchy.TaggedPrune
open Filter Real
open scoped Classical BigOperators

/-- At every width above the lower power, a fixed polylogarithmic selector
overhead consumes at most the requested fraction of the payload. -/
theorem eventually_absorb {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (d : ℝ) :
    ∀ᶠ h : ℕ in atTop, ∀ w n : ℝ, (h:ℝ)^(1+κ) ≤ w → 0 ≤ n →
      n*h*(Real.log h)^d ≤ ε*n*w := by
  have little := (isLittleO_log_rpow_rpow_atTop d hκ).bound hε
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually little,
    eventually_ge_atTop (2:ℕ)] with h bound h₂
  intro w n hw hn
  have hp : 1 < (h:ℝ) := by exact_mod_cast (show 1 < h by omega)
  change ‖(Real.log (h:ℝ))^d‖ ≤ ε*‖(h:ℝ)^κ‖ at bound
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Real.log_pos hp).le _),
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at bound
  rw [Real.rpow_add (zero_lt_one.trans hp), Real.rpow_one] at hw
  calc
    _ ≤ n*h*(ε*(h:ℝ)^κ) := mul_le_mul_of_nonneg_left bound (mul_nonneg hn (Nat.cast_nonneg _))
    _ = ε*n*((h:ℝ)*(h:ℝ)^κ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (mul_nonneg hε.le hn)

/-- Even after paying the ordinary-sum price, half the original pruning
discount remains, uniformly at every allowed width. Here the entropy counts
both the selector and the exposed permutation. -/
theorem eventually_half_gap {κ C : ℝ} (hκ : 0<κ) (hC : 0<C)
    {k M : ℕ} (hk : 0<k) (hM : 0<M) (d : ℝ) :
    ∀ᶠ h : ℕ in atTop, ∀ (w B : ℕ), (h:ℝ)^(1+κ) ≤ w →
      (h:ℝ)*2^h+B ≤ C*((2:ℝ)^h*h*(Real.log h)^d) →
      (2:ℝ)^h*w/(2*M) ≤ (2:ℝ)^h*w/M - 2*(k:ℝ)*((h:ℝ)*2^h+B) := by
  have hk' : 0<(k:ℝ) := Nat.cast_pos.mpr hk
  have hM' : 0<(M:ℝ) := Nat.cast_pos.mpr hM
  let ε : ℝ := 1/(4*(k:ℝ)*(M:ℝ)*C)
  have hε : 0<ε := by dsimp [ε]; positivity
  filter_upwards [eventually_absorb hκ hε d] with h bound
  intro w B hw enc
  have absorbed := bound w ((2:ℝ)^h) hw (by positivity)
  have cost := calc
    2*(k:ℝ)*((h:ℝ)*2^h+B) ≤ 2*(k:ℝ)*(C*((2:ℝ)^h*h*(Real.log h)^d)) :=
      mul_le_mul_of_nonneg_left enc (by positivity)
    _ = (2*(k:ℝ)*C)*((2:ℝ)^h*h*(Real.log h)^d) := by ring
    _ ≤ (2*(k:ℝ)*C)*(ε*2^h*w) := mul_le_mul_of_nonneg_left absorbed (by positivity)
    _ = (2:ℝ)^h*w/(2*M) := by dsimp only [ε]; field_simp; ring
  have half : (2:ℝ)^h*w/M = (2:ℝ)^h*w/(2*M) + (2:ℝ)^h*w/(2*M) := by field_simp; ring
  linarith only [cost,half]


end Hierarchy.TaggedPrune

end
end OAI
