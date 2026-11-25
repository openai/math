import Mathlib

/-! # Dyadic times for iterated midpoint segments

Rounding a nonnegative time down to the grid of mesh `2⁻ⁿ` gives nested
adjacent cells and converges to the original time.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter Topology

namespace DyadicSegment

/-- The grid index immediately to the left of a nonnegative time. -/
def index (n : ℕ) (t : ℝ) : ℕ := ⌊(2 : ℝ) ^ n * t⌋₊

@[simp] theorem index_zero (n : ℕ) : index n 0 = 0 := by simp [index]

@[simp] theorem index_one (n : ℕ) : index n 1 = 2 ^ n := by
  simp only [index, mul_one]
  exact_mod_cast Nat.floor_natCast (R := ℝ) (2 ^ n)

theorem index_mono (n : ℕ) : Monotone (index n) :=
  fun _ _ h ↦ Nat.floor_mono (mul_le_mul_of_nonneg_left h (by positivity))

theorem index_le (n : ℕ) {t : ℝ} (ht : t ≤ 1) : index n t ≤ 2 ^ n := by
  simpa using index_mono n ht

theorem index_refine (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    index (n + 1) t = 2 * index n t ∨ index (n + 1) t = 2 * index n t + 1 := by
  have hfloor : (index n t : ℝ) ≤ 2 ^ n * t := Nat.floor_le (by positivity)
  have hsucc : 2 ^ n * t < (index n t : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo : 2 * index n t ≤ index (n + 1) t := by
    apply Nat.le_floor
    push_cast
    rw [pow_succ]
    linarith
  have hhi : index (n + 1) t < 2 * index n t + 2 := by
    apply (Nat.floor_lt (by positivity)).2
    push_cast
    rw [pow_succ]
    linarith
  omega

theorem tendsto_index_div {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ (index n t : ℝ) / 2 ^ n) atTop (𝓝 t) := by
  have hmesh : Tendsto (fun n : ℕ ↦ 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using (tendsto_const_nhds (x := t)).sub hmesh) tendsto_const_nhds
  · intro n
    have h := Nat.lt_floor_add_one ((2 : ℝ) ^ n * t)
    change (2 : ℝ) ^ n * t < (index n t : ℝ) + 1 at h
    change t - 1 / 2 ^ n ≤ (index n t : ℝ) / 2 ^ n
    rw [le_div_iff₀ (by positivity), sub_mul, div_mul_cancel₀ _ (by positivity)]
    linarith
  · intro n
    apply (div_le_iff₀ (by positivity)).2
    rw [mul_comm]
    exact Nat.floor_le (by positivity)

end DyadicSegment

end

end SpectralBooks
end LinearAlgebra
end OAI
