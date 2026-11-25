import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentPath
import OAI.Optimization.LinearProgramming.PriceGame.MarketDenominator
import OAI.Optimization.LinearProgramming.RAM.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.Order.Lemmas

/-! # Rational bounds for transshipment

All Bellman computations use sums of inputs with a common denominator. Bounding
both the grid and the absolute value controls the reduced binary representation.
In a unit augmentation the dummy edge costs zero. The new target terminal value
is the old source potential plus one. The size bound below is additive in
the number of augmentations, even for the potentials carried from one call to the next.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace NumberBounds
open Quiver
open OAI.Optimization.LinearProgramming.PriceGame.Market.Potentials
open OAI.Optimization.LinearProgramming.PriceGame.Market.Augment

def OnGrid (D : ℕ) (x : ℚ) : Prop := ∃ z : ℤ, (D : ℚ) * x = z

theorem grid_zero (D : ℕ) : OnGrid D 0 := ⟨0, by simp⟩
theorem grid_one (D : ℕ) : OnGrid D 1 := ⟨Int.ofNat D, by simp⟩

theorem OnGrid.add {D : ℕ} {x y : ℚ} (hx : OnGrid D x) (hy : OnGrid D y) : OnGrid D (x + y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by simp [mul_add, ha, hb]⟩

theorem OnGrid.neg {D : ℕ} {x : ℚ} (hx : OnGrid D x) : OnGrid D (-x) := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨-a, by simp [ha]⟩

theorem OnGrid.abs {D : ℕ} {x : ℚ} (hx : OnGrid D x) : OnGrid D |x| := by
  rcases le_total 0 x with h | h
  · simpa [abs_of_nonneg h] using hx
  · simpa [abs_of_nonpos h] using hx.neg

theorem grid_iff_den_dvd {D : ℕ} (hD : 0 < D) (x : ℚ) :
    OnGrid D x ↔ x.den ∣ D := by
  constructor
  · rintro ⟨z, hz⟩
    have heq : x = Rat.divInt z (D : ℤ) := by
      rw [Rat.divInt_eq_div, Int.cast_natCast]
      apply (eq_div_iff (by exact_mod_cast hD.ne')).mpr
      rwa [mul_comm]
    have hh := Rat.den_dvd z (D : ℤ)
    rw [← heq] at hh
    exact_mod_cast hh
  · rintro ⟨k, hk⟩
    have he : (x.num : ℚ) = x * (x.den : ℚ) :=
      (div_eq_iff (by exact_mod_cast x.den_ne_zero)).mp x.num_div_den
    refine ⟨x.num * (k : ℤ), ?_⟩
    simp only [hk, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, he]
    ring

theorem numerator_le_of_abs_le {x : ℚ} {B : ℕ} (hb : |x| ≤ B) :
    x.num.natAbs ≤ B * x.den := by
  have he : (x.num : ℚ) = x * (x.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast x.den_ne_zero)).mp x.num_div_den
  have h := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α := ℚ) x.den)
  have hnum : (x.num.natAbs : ℚ) = |(x.num : ℚ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hh : (x.num.natAbs : ℚ) ≤ (B : ℚ) * (x.den : ℚ) := by
    rw [hnum, he, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℚ) x.den)]
    exact h
  exact_mod_cast hh

private theorem log2_le_size (a : ℕ) : a.log2 ≤ a.size := by
  rcases Nat.eq_zero_or_pos a with rfl | h
  · decide
  · exact ((Nat.log2_lt h.ne').mpr (Nat.lt_size_self a)).le

private theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_right b (Nat.lt_size_self a).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (Nat.two_pow_pos _))

/-- Reduced numerator and denominator encoding length on a fixed grid. -/
theorem ratBits_grid {D B : ℕ} {x : ℚ} (hD : 0 < D) (hx : OnGrid D x) (hb : |x| ≤ B) :
    RAM.ratBits x ≤ 3 + B.size + 2 * D.size := by
  have hd := Nat.le_of_dvd hD ((grid_iff_den_dvd hD x).mp hx)
  have hn := (numerator_le_of_abs_le hb).trans (Nat.mul_le_mul_left B hd)
  have h1 := (log2_le_size x.num.natAbs).trans ((Nat.size_le_size hn).trans (size_mul_le B D))
  have h2 := (log2_le_size x.den).trans (Nat.size_le_size hd)
  unfold RAM.ratBits
  omega

variable {V : Type*} [Quiver V] (w : ∀ {a b : V}, (a ⟶ b) → ℚ)

/-- At the target the previous target potential cancels. All other terminal
values are copied, so a zero-cost direct path gives at most one added unit. -/
theorem targetReward_at [DecidableEq V] (π : V → ℚ) {s t : V} (ref : Path s t) :
    targetReward w π ref t = π s - ref.addWeight w + 1 := by
  simp [targetReward]
  ring

theorem terminal_grid_of_direct [DecidableEq V] {D : ℕ} (π : V → ℚ)
    (hg : ∀ v, OnGrid D (π v)) {s t : V} (ref : Path s t) (h0 : ref.addWeight w = 0)
    (v : V) : OnGrid D (targetReward w π ref v) := by
  by_cases h : v = t
  · subst v
    rw [targetReward_at, h0, sub_zero]
    exact (hg s).add (grid_one D)
  · simpa [targetReward, h] using hg v

theorem terminal_abs_of_direct [DecidableEq V] {U : ℚ} (π : V → ℚ)
    (hg : ∀ v, |π v| ≤ U) {s t : V} (ref : Path s t) (h0 : ref.addWeight w = 0)
    (v : V) : |targetReward w π ref v| ≤ U + 1 := by
  by_cases h : v = t
  · subst v
    rw [targetReward_at, h0, sub_zero]
    exact (abs_add_le _ _).trans (by simpa using add_le_add_right (hg s) 1)
  · rw [targetReward, ite_eq_right h, add_zero]
    linarith [hg v]

variable [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]

theorem intermediate_abs {C U : ℚ} (hC : 0 ≤ C)
    (hc : ∀ {a b : V} (e : a ⟶ b), |w e| ≤ C)
    (r : V → ℚ) (hr : ∀ v, |r v| ≤ U) (k : ℕ) (v : V) :
    |value w r k v| ≤ (k : ℚ) * C + U := by
  obtain ⟨j, p, hp, he⟩ := value_attained w r k v
  rw [he]
  have hk : (p.length : ℚ) ≤ (k : ℚ) := by exact_mod_cast hp
  have bound := (abs_weight_le w C hc p).trans (mul_le_mul_of_nonneg_right hk hC)
  exact (abs_add_le _ _).trans (add_le_add bound (hr j))

theorem intermediate_grid {D : ℕ} (hc : ∀ {a b : V} (e : a ⟶ b), OnGrid D (w e))
    (r : V → ℚ) (hr : ∀ v, OnGrid D (r v)) (k : ℕ) (v : V) : OnGrid D (value w r k v) := by
  obtain ⟨j, p, _, he⟩ := value_attained w r k v
  rw [he]
  exact OnGrid.add (weight_denominator w D hc p) (hr j)

end NumberBounds
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
