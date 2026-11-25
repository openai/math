import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Integer clocks for a recursive real-valued fare

Rounding each scaled fare down pays for the full docket of child requests
without introducing a rounding error proportional to the number of children.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

variable {X : Type*}

/-- Scaled, rounded child fares sum to at most the scaled real fare of the docket. -/
theorem sum_floor_fare_le (D : ℕ) (fare : X → ℝ) (hfare : ∀ x, 0 ≤ fare x)
    (children : List X) :
    (((children.map (fun y => ⌊(D : ℝ) * fare y⌋₊)).sum : ℕ) : ℝ) ≤
      D * (children.map fare).sum := by
  induction children with
  | nil => simp
  | cons y children ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, mul_add]
    exact add_le_add (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (hfare y))) ih

/-- A fixed integral scale absorbs a linear local cost using the fractional
slack in the total fare. The recurrence counts each child at unit coefficient. -/
theorem exists_floor_clock (w : X → ℕ) (children : X → List X) (fare : X → ℝ)
    (hfare : ∀ x, 0 ≤ fare x) (C ε : ℝ) (hε : 0 < ε)
    (localCost : ∀ x, (w x : ℝ) + 1 ≤ C * fare x)
    (slack : ∀ x, ((children x).map fare).sum + ε * fare x ≤ fare x) :
    ∃ D : ℕ, ∀ x, w x + 1 + ((children x).map (fun y => ⌊(D : ℝ) * fare y⌋₊)).sum ≤
      ⌊(D : ℝ) * fare x⌋₊ := by
  obtain ⟨D, hD⟩ := exists_nat_gt (C / ε)
  have hscale : C ≤ (D : ℝ) * ε := ((div_lt_iff₀ hε).mp hD).le
  refine ⟨D, fun x => (Nat.le_floor_iff (mul_nonneg (Nat.cast_nonneg D) (hfare x))).mpr ?_⟩
  simp only [Nat.cast_add, Nat.cast_one]
  have work := (localCost x).trans (mul_le_mul_of_nonneg_right hscale (hfare x))
  have cap := mul_le_mul_of_nonneg_left (slack x) (Nat.cast_nonneg D)
  rw [mul_add, ← mul_assoc] at cap
  exact (add_le_add work (sum_floor_fare_le D fare hfare (children x))).trans (by
    simpa only [add_comm] using cap)

/-- The rounded clock is bounded uniformly by the integer ceiling of the fare. -/
theorem floor_clock_le_mul_ceil (D : ℕ) {fare : ℝ} (hfare : 0 ≤ fare) :
    ⌊(D : ℝ) * fare⌋₊ ≤ D * ⌈fare⌉₊ := by
  exact_mod_cast (Nat.floor_le (mul_nonneg (Nat.cast_nonneg D) hfare)).trans
    (mul_le_mul_of_nonneg_left (Nat.le_ceil fare) (Nat.cast_nonneg D))

end InterchangeSpace

end NearSquareRoot
end Computability
end OAI
