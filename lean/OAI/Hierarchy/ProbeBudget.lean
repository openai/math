import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

namespace OAI
/-! # The capacity charge and the physical catalyst account -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

def capacity (p q Q t len : ℝ) : ℝ :=
  if t=0 then 0 else t^p * max (len^(-q)) (len^(-Q))

variable {I : Type*} [Fintype I]

/-- The size and catalyst allowances of a single accepted term, after
aggregating the widths on its installed links. -/
def TermBudget (p q Q Λ : ℝ) (n w M Nc : ℕ) (t len y : I → ℝ) : Prop :=
  ∑ i, (len i*y i + Λ*capacity p q Q (t i) (len i)) ≤
    10*(n:ℝ) + 2*(M:ℝ)*(Nc:ℝ)/(w:ℝ)

@[simp] theorem capacity_zero (p q Q len : ℝ) : capacity p q Q 0 len = 0 := by simp [capacity]

@[simp] theorem capacity_unit (p q Q t : ℝ) (ht : 0<t) : capacity p q Q t 1 = t^p := by
  simp [capacity,ht.ne']

/-- Returning every unused bit on its own pair's reserved route exactly
restores the baseline credit. Parallel directions may have different
prices and any finite multiplicities. -/
theorem catalyst_account {C : Type*} [Fintype C] (price : C → ℝ)
    (reserved used : C → ℕ) (within : ∀ c, used c ≤ reserved c)
    (cost budget : ℝ) (paid : cost - ∑ c, price c * (used c : ℝ) ≤ budget) :
    cost + ∑ c, price c * ((reserved c-used c : ℕ) : ℝ) ≤
      budget + ∑ c, price c * (reserved c : ℝ) := by
  have split (c : C) : price c * ((reserved c-used c : ℕ):ℝ) =
      price c * (reserved c : ℝ) - price c * (used c : ℝ) := by
    rw [Nat.cast_sub (within c), mul_sub]
  simp_rw [split]
  rw [Finset.sum_sub_distrib]
  linarith

/-- Multiplication by the number of payloads converts the normalized
ledger into the charge used by the shorter-call recurrence. -/
theorem termBudget_of_normalized (p q Q Λ : ℝ) (n w M Nc : ℕ) (t len y : I → ℝ)
    (hn : 0<n) (hw : 0<w)
    (account : (∑ i, (len i*y i + Λ*capacity p q Q (t i) (len i)))/(n:ℝ) ≤
      10 + 2*(M:ℝ)*(Nc:ℝ)/((n:ℝ)*(w:ℝ))) :
    TermBudget p q Q Λ n w M Nc t len y := by
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hw' : (0:ℝ)<w := Nat.cast_pos.mpr hw
  unfold TermBudget
  apply ((div_le_iff₀ hn').mp account).trans_eq
  field_simp


end
end Hierarchy.AdaptiveProbe

end OAI
