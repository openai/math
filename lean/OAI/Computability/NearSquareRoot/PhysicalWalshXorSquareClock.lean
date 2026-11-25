import OAI.Computability.NearSquareRoot.PhysicalWalshFrontClock

/-! # The square-log cutoff in the selected-width XOR clock

A guard of length at most both the moving field width and the square of the
header logarithm costs one logarithmic factor at every exponent above one half.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorSquare

open PhysicalWalshNode ElementarySchedule

/-- The two truncations together bound the guard by the geometric mean.
The bound holds at zero width and at the endpoint exponent one half. -/
theorem min_sq_rpow {ρ : ℝ} (half : 1/2 ≤ ρ) (L z : ℕ) :
    ((min L (z^2) : ℕ) : ℝ) ≤ (L:ℝ)^ρ * z := by
  rcases Nat.eq_zero_or_pos L with rfl | pos
  · simp [Real.zero_rpow (show ρ ≠ 0 by linarith)]
  have natBound := Nat.mul_le_mul (min_le_left L (z^2)) (min_le_right L (z^2))
  have sqBound : (((min L (z^2) : ℕ):ℝ))^2 ≤ (L:ℝ)*(z:ℝ)^2 := by
    rw [sq]
    exact_mod_cast natBound
  have square : (((min L (z^2) : ℕ):ℝ))^2 ≤ (Real.sqrt (L:ℝ)*(z:ℝ))^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg L)]
    exact sqBound
  have le := (sq_le_sq₀ (by positivity) (by positivity)).mp square
  rw [Real.sqrt_eq_rpow] at le
  have one : (1:ℝ) ≤ L := by exact_mod_cast pos
  exact le.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one half) (Nat.cast_nonneg z))

theorem guard_rate {ρ : ℝ} (half : 1/2 ≤ ρ) (L Q : ℕ) :
    ((min L ((Nat.clog 2 (Q+1))^2) : ℕ):ℝ) ≤ ((L+1:ℕ):ℝ)^ρ * Nat.clog 2 (Q+1) := by
  apply (min_sq_rpow half L _).trans
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (Nat.cast_nonneg L) (by exact_mod_cast Nat.le_succ L) (by linarith))
    (Nat.cast_nonneg _)

theorem elementary_rate {ρ : ℝ} (half : 1/2 ≤ ρ) {L Q : ℕ} (small : L ≤ (Nat.clog 2 (Q+1))^2) :
    (L:ℝ) ≤ ((L+1:ℕ):ℝ)^ρ * Nat.clog 2 (Q+1) := by
  simpa only [min_eq_left small] using guard_rate half L Q

/-- The truncated elementary transfer on the actual array pays a single
logarithm of its compact header scale. -/
theorem prefix_bound (A : ℕ) {ρ : ℝ} (half : 1/2 ≤ ρ) (s : Shape) :
    (ElementarySweep.prefixExtra A
      (fun t => min (slotWidth A t) ((Nat.clog 2 (Header.scale A t+1))^2)) s:ℝ) ≤
      3*RouterClock.unit A ρ s := by
  let L := slotWidth A s
  let Q := Header.scale A s
  let z := Nat.clog 2 (Q+1)
  let g := min L (z^2)
  have edge : (g:ℝ) ≤ (L:ℝ)^ρ*z := min_sq_rpow half L z
  have p : 0 ≤ (L:ℝ)^ρ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h := edge.trans (mul_le_mul_of_nonneg_left (FrontClock.clog_le Q) p)
  have one := RouterClock.one_le_logWidth Q
  change (g:ℝ) ≤ (L:ℝ)^ρ*(3*RouterClock.logWidth Q) at h
  have scans : (g:ℝ)+1 ≤ 3*RouterClock.logWidth Q*(1+(L:ℝ)^ρ) := by linarith only [one,h]
  change (((g+1)*RouterClock.rawVolume A s : ℕ):ℝ) ≤ _
  push_cast
  calc
    _ ≤ (3*RouterClock.logWidth Q*(1+(L:ℝ)^ρ))*(RouterClock.rawVolume A s:ℝ) :=
      mul_le_mul_of_nonneg_right scans (Nat.cast_nonneg _)
    _ = _ := by unfold RouterClock.unit; dsimp only [L,Q]; ring

/-- Every transfer in the elementary branch lies below the truncated guard. -/
theorem small_bound (A : ℕ) {ρ : ℝ} (half : 1/2 ≤ ρ) (s : Shape)
    (small : slotWidth A s ≤ (Nat.clog 2 (Header.scale A s+1))^2) :
    (ElementarySweep.extra A s : ℝ) ≤ 3*RouterClock.unit A ρ s := by
  simpa only [ElementarySweep.extra,ElementarySweep.prefixExtra,min_eq_left small] using prefix_bound A half s

/-- The same clock covers the full two-way front gate after testing the
square-log threshold. The multiplicative constant is independent of the
table degree and controller scale. -/
theorem switch_bound {a : ℕ} (W : ℕ) {ρ : ℝ} (half : 1/2 ≤ ρ) (upper : ρ ≤ 1) (s : Shape) :
    let A := a+1
    ((if slotWidth A s ≤ (Nat.clog 2 (Header.scale A s+1))^2 then ElementarySweep.extra A s
      else XorThreshold.gateClock ρ (slotWidth A s) (FrontClock.volume A W s) : ℕ):ℝ) ≤
      5505*RouterClock.unit A ρ s := by
  intro A
  split_ifs with small
  · exact (small_bound A half s small).trans (mul_le_mul_of_nonneg_right (by norm_num)
      (zero_le_one.trans (RouterClock.one_le_unit A ρ s)))
  · exact FrontClock.large_bound W (by linarith) upper s

/-- Charge the elementary square-log guard, the rectangular slot exchange,
and the front XOR to the original occupied-node recurrence. -/
theorem combined_clock {A : ℕ} (arity : 2 ≤ A) {ρ : ℝ} (half : 1/2 ≤ ρ)
    {front : Shape → ℕ} {B : ℝ} (hB : 0 ≤ B)
    (central : ∀ s, withinWidth A s → (front s:ℝ) ≤ B*RouterClock.unit A ρ s) (s : Shape)
    (admit : withinWidth A s) :
    ((ElementarySweep.prefixExtra A (fun t => min (slotWidth A t) ((Nat.clog 2 (Header.scale A t+1))^2)) s
      + SlotSwap.wideExtra ρ A s + front s : ℕ):ℝ) ≤
      localTime A ρ (74*(4+(2:ℝ)^ρ+B)) (RouterClock.logWidth s.w) 0 s.level (bitVolume A s) := by
  have positive : 0 ≤ ρ := by linarith
  apply RouterClock.unit_local arity positive (by positivity : 0 ≤ 4+(2:ℝ)^ρ+B) admit
  have guardCost := prefix_bound A half s
  have wideCost := RouterClock.wide_bound (by omega : 0 < A) positive s
  have frontCost := central s admit
  push_cast
  linarith only [guardCost,wideCost,frontCost]

end PhysicalWalsh.XorSquare

end NearSquareRoot
end Computability
end OAI
