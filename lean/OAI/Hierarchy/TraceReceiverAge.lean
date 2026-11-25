import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.NormNum

namespace OAI
/-! # A receiver workspace age for every sufficiently large native word width -/

namespace Hierarchy.TraceAdmission
open Filter

private theorem age_exists (w : ℕ) : ∃ v : ℕ, 4*w≤v^10 :=
  ⟨4*w,Nat.le_self_pow (by decide) _⟩

/-- The least age whose fixed workspace stride holds four native-width scales. -/
def receiverAge (w : ℕ) := Nat.find (age_exists w)

theorem receiverAge_lower (w : ℕ) : 4*w≤(receiverAge w)^10 := Nat.find_spec (age_exists w)

theorem receiverAge_tendsto : Tendsto receiverAge atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (k^10+1)] with w hw
  by_contra no
  have p := Nat.pow_le_pow_left (by omega : receiverAge w≤k) 10
  have := receiverAge_lower w
  omega

/-- For ages at least sixty-four a single step increases the tenth power by at most a quarter. -/
private theorem next_tenth {v : ℕ} (large : 64≤v) : 4*(v+1)^10≤5*v^10 := by
  have p := Nat.pow_le_pow_left (by omega : 64*(v+1)≤65*v) 10
  rw [mul_pow,mul_pow] at p
  have scaled : 4*(65:ℕ)^10≤5*64^10 := by decide
  have step : 64^10*(4*(v+1)^10)≤64^10*(5*v^10) := calc
    _ = 4*(64^10*(v+1)^10) := by ac_rfl
    _ ≤ 4*(65^10*v^10) := Nat.mul_le_mul_left _ p
    _ = (4*65^10)*v^10 := by ac_rfl
    _ ≤ (5*64^10)*v^10 := Nat.mul_le_mul_right _ scaled
    _ = _ := by ac_rfl
  exact Nat.le_of_mul_le_mul_left step (by decide)

/-- The selection works for every width above the cutoff. -/
theorem receiverAge_chart (w : ℕ) (large : 64^10≤w) :
    4*w≤(receiverAge w)^10 ∧ (receiverAge w)^10≤5*w := by
  have low := receiverAge_lower w
  refine ⟨low,?_⟩
  have ageLarge : 64<receiverAge w := by
    by_contra no
    have := Nat.pow_le_pow_left (by omega : receiverAge w≤64) 10
    omega
  obtain ⟨v,hv⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : receiverAge w≠0)
  have before : v<receiverAge w := by omega
  have prior : ¬ 4*w≤v^10 := Nat.find_min (age_exists w) before
  rw [hv]
  change (v+1)^10≤5*w
  have := next_tenth (by omega : 64≤v)
  omega

theorem eventually_receiverAge :
    ∀ᶠ w : ℕ in atTop, 4*w≤(receiverAge w)^10 ∧ (receiverAge w)^10≤5*w := by
  filter_upwards [eventually_ge_atTop (64^10)] with w hw using receiverAge_chart w hw

end Hierarchy.TraceAdmission

end OAI
