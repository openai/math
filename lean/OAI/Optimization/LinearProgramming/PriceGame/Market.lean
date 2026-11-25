import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import OAI.Optimization.LinearProgramming.PriceGame.MarketBid

/-! # Balanced prices from a market transshipment (Section 4)

The two orientations at an expert encode its sign. The vertex `none` is the dummy
for the outside option, whose score is zero. Residual feasibility and tightness on
positive-flow arcs yield the maximizing allocations in the price game.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market

open scoped BigOperators

variable {E G : Type*}

/-- The coefficient with which a good's price enters the expert's score. -/
def side (pos : E → Bool) (e : E) : ℚ := if pos e then 1 else -1

/-- The dummy is available to every expert. -/
def eligible (accepts : E → G → Prop) (e : E) : Option G → Prop
  | none => True
  | some i => accepts e i

/-- Scores, including the outside option. -/
def score (pos : E → Bool) (c : E → G → ℚ) (y : G → ℚ) (e : E) : Option G → ℚ
  | none => 0
  | some i => c e i - side pos e * y i

/-- The normalized good price, independent of an overall potential shift. -/
def price (π : Option G → ℚ) (i : G) : ℚ := π none - π (some i)

/-- Divide the integer mass assigned to an option by this expert's supply. -/
def fraction (f : E → Option G → ℕ) (qty : E → ℕ) (e : E) (o : Option G) : ℚ :=
  (f e o : ℚ) / (qty e : ℚ)

/-- Residual-arc inequalities, in the two possible orientations. Equality on a
positive-flow arc follows by applying the reverse residual-arc inequality. -/
structure ResidualPotentials (pos : E → Bool) (accepts : E → G → Prop)
    (c : E → G → ℚ) (f : E → Option G → ℕ) (expert : E → ℚ) (opt : Option G → ℚ) : Prop where
  forward : ∀ e o, eligible accepts e o → bid c e o ≤ side pos e * (expert e - opt o)
  backward : ∀ e o, 0 < f e o → side pos e * (expert e - opt o) ≤ bid c e o

/-- The substantive conclusions for all maximizing choices and the signed balances
at individual goods in the balanced-prices lemma. -/
structure Balanced [Fintype E] [Fintype G] (pos : E → Bool) (L : E → ℚ)
    (accepts : E → G → Prop) (c : E → G → ℚ) (y : G → ℚ) (f : E → Option G → ℚ) : Prop where
  nonneg : ∀ e o, 0 ≤ f e o
  unit : ∀ e, ∑ o, f e o = 1
  allowed : ∀ e o, 0 < f e o → eligible accepts e o
  maximizes : ∀ e o, 0 < f e o → ∀ o', eligible accepts e o →
    eligible accepts e o' → score pos c y e o' ≤ score pos c y e o
  clears : ∀ i, ∑ e, L e * side pos e * f e (some i) = 0

theorem score_le_of_residual {pos : E → Bool} {c : E → G → ℚ} {accepts : E → G → Prop}
    {f : E → Option G → ℕ} {p : E → ℚ} {π : Option G → ℚ}
    (h : ResidualPotentials pos accepts c f p π)
    (e : E) (o : Option G) (ha : eligible accepts e o) :
    score pos c (price π) e o ≤ side pos e * (p e - π none) := by
  have hf := h.forward e o ha
  cases o with
  | none => exact hf
  | some i =>
    change c e i ≤ _ at hf
    change c e i - side pos e * (π none - π (some i)) ≤ _
    linarith only [hf]

theorem score_eq_of_used {pos : E → Bool} {c : E → G → ℚ} {accepts : E → G → Prop}
    {f : E → Option G → ℕ} {p : E → ℚ} {π : Option G → ℚ}
    (h : ResidualPotentials pos accepts c f p π)
    (e : E) (o : Option G) (ha : eligible accepts e o) (hp : 0 < f e o) :
    score pos c (price π) e o = side pos e * (p e - π none) := by
  apply le_antisymm (score_le_of_residual h e o ha)
  have hb := h.backward e o hp
  cases o with
  | none => exact hb
  | some i =>
    change _ ≤ c e i at hb
    change _ ≤ c e i - side pos e * (π none - π (some i))
    linarith only [hb]

/-- Normalization of an integer allocation gives a multiple of the prescribed
unit, even if that denominator has redundant factors. -/
theorem scaled_fraction {L : E → ℚ} (f : E → Option G → ℕ) (qty : E → ℕ)
    {Q : ℕ} (hQ : 0 < Q) (hqty : ∀ e, 0 < qty e)
    (hscale : ∀ e, (qty e : ℚ) = (Q : ℚ) * L e) (e : E) (o : Option G) :
    L e * fraction f qty e o = (f e o : ℚ) / (Q : ℚ) := by
  have hden : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have he : (qty e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hqty e).ne'
  unfold fraction
  field_simp
  rw [hscale]
  ring

/-- Extract a complete balanced allocation and prices from a primal and residual
dual network solution. All comparisons include the dummy option. -/
theorem balanced_of_residual [Fintype E] [Fintype G]
    {pos : E → Bool} {L : E → ℚ} {accepts : E → G → Prop}
    {c : E → G → ℚ} {qty : E → ℕ} {f : E → Option G → ℕ} {p : E → ℚ} {π : Option G → ℚ}
    {Q : ℕ} (hQ : 0 < Q) (hq : ∀ e, 0 < qty e) (hs : ∀ e, (qty e : ℚ) = (Q : ℚ) * L e)
    (hrow : ∀ e, ∑ o, f e o = qty e)
    (hvalid : ∀ e o, 0 < f e o → eligible accepts e o)
    (hflow : ∀ i, ∑ e, side pos e * (f e (some i) : ℚ) = 0)
    (hpot : ResidualPotentials pos accepts c f p π) :
    Balanced pos L accepts c (price π) (fraction f qty) := by
  have hpos (e : E) (o : Option G) (h : 0 < fraction f qty e o) : 0 < f e o := by
    by_contra! hz
    simp [fraction, Nat.le_zero.mp hz] at h
  refine ⟨fun e o => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_, ?_, ?_, ?_⟩
  · intro e
    simp only [fraction, ← Finset.sum_div, ← Nat.cast_sum, hrow]
    exact div_self (Nat.cast_ne_zero.mpr (hq e).ne')
  · exact fun e o h => hvalid e o (hpos e o h)
  · intro e o ho o' ha ha'
    rw [score_eq_of_used hpot e o ha (hpos e o ho)]
    exact score_le_of_residual hpot e o' ha'
  · intro i
    calc
      _ = ∑ e, (side pos e * (f e (some i) : ℚ)) / (Q : ℚ) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [mul_right_comm, scaled_fraction f qty hQ hq hs]
        ring
      _ = 0 := by rw [← Finset.sum_div, hflow, zero_div]

/-- Normalizing path-length potentials preserves every common denominator of
the arc lengths, including a nonminimal common denominator. -/
theorem price_denominator (π : Option G → ℚ) (D : ℕ)
    (h : ∀ o, ∃ z : ℤ, (D : ℚ) * π o = z) (i : G) :
    ∃ z : ℤ, (D : ℚ) * price π i = z := by
  obtain ⟨u, hu⟩ := h none
  obtain ⟨v, hv⟩ := h (some i)
  refine ⟨u - v, ?_⟩
  simp [price, mul_sub, hu, hv]

/-- The absolute price bound after fixing the dummy potential to zero. -/
theorem abs_price_le (π : Option G → ℚ) {B : ℚ}
    (h : ∀ o, |π o| ≤ B) (i : G) : |price π i| ≤ 2 * B := by
  calc
    _ ≤ |π none| + |π (some i)| := abs_sub _ _
    _ ≤ 2 * B := by linarith [h none, h (some i)]

/-- Goods balance separately, so arbitrary signed feedback on the goods
cancels after weighting by the real allocations. -/
theorem feedback_cancels [Fintype E] [Fintype G] {pos : E → Bool}
    {L : E → ℚ} {accepts : E → G → Prop} {c : E → G → ℚ} {y : G → ℚ}
    {f : E → Option G → ℚ} (h : Balanced pos L accepts c y f) (z : G → ℚ) :
    ∑ e, L e * (∑ i, side pos e * f e (some i) * z i) = 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  calc
    _ = (∑ e, L e * side pos e * f e (some i)) * z i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = 0 := by rw [h.clears, zero_mul]

end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
