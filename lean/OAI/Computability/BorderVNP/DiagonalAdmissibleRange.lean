import OAI.Computability.BorderVNP.DiagonalAdvice

/-! # Intersecting processor bounds before the two stretch exponents are chosen -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter

/-- A single processor-length threshold covers every batch in the stated range. -/
def AdmissibleRange (ω : ℝ) (p : ℕ → ℕ → Prop) :=
  ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r:ℝ) ≤ 2^((n:ℝ)^ω) → p n r

/-- Shrinking the batch exponent preserves all the uniform estimates. -/
theorem AdmissibleRange.shrink {p : ℕ → ℕ → Prop} {u v : ℝ}
    (h : AdmissibleRange v p) (huv : u ≤ v) : AdmissibleRange u p := by
  filter_upwards [h,eventually_ge_atTop 1] with n hn one
  intro r hr room
  exact hn r hr (room.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast one : (1:ℝ) ≤ n) huv)))

theorem stretch_one (ρ : ℝ) (n : ℕ) : 1 ≤ stretch ρ n :=
  Nat.le_floor (show ((1:ℕ):ℝ) ≤ (2:ℝ)^((n:ℝ)^ρ) from
    by simpa using Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Evaluate a previously chosen length window at the actual rounded team size. -/
theorem AdmissibleRange.stretched {p : ℕ → ℕ → Prop} {ω ρ : ℝ}
    (h : AdmissibleRange ω p) (inside : ρ ≤ ω) :
    ∀ᶠ n : ℕ in atTop, p n (stretch ρ n) := by
  filter_upwards [h.shrink inside] with n hn
  exact hn _ (stretch_one ..) (Nat.floor_le (by positivity))

end Diagonal

end BorderVNP
end Computability
end OAI
