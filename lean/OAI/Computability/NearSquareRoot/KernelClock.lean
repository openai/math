import OAI.LinearAlgebra.FiniteFourier.PrimeWindow
import Mathlib.Data.Rat.Floor

/-! # Integer generation of the repair period

The period used by the binary repair pencil is a power of two. Its
logarithm can be generated with integer square tests and rational
rounding before the pencil is searched. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PencilSearch

open OAI.LinearAlgebra.FiniteFourier

private theorem exists_square_ge (n : ℕ) : ∃ k : ℕ, n ≤ k ^ 2 :=
  ⟨n + 1, by nlinarith⟩

/-- Least integer radius whose square covers the supplied count. -/
def ceilSqrt (n : ℕ) : ℕ := Nat.find (exists_square_ge n)

theorem ceilSqrt_eq (n : ℕ) : ceilSqrt n = ⌈Real.sqrt n⌉₊ := by
  apply le_antisymm
  · apply Nat.find_min'
    have h := (Real.sqrt_le_iff.mp (Nat.le_ceil (Real.sqrt n))).2
    exact_mod_cast h
  · apply Nat.ceil_le.mpr
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by exact_mod_cast Nat.find_spec (exists_square_ge n)⟩

/-- The paper's binary count window, with integer radius and exact rational endpoints. -/
def clockDegree (m : ℕ) : ℕ :=
  let r : ℕ := ceilSqrt (2 * m * Nat.clog 2 (2 * m))
  let mean : ℚ := (m : ℚ) / 2
  (⌈mean + r⌉ - ⌊mean - r⌋).toNat

theorem clockDegree_eq (m : ℕ) : clockDegree m = repairWindowDegree 2 m := by
  let r := ceilSqrt (2 * m * Nat.clog 2 (2 * m))
  have hr : repairWindowRadius 2 m = r := by
    simp only [r, repairWindowRadius, repairWindowR, Nat.reduceSub, one_mul, ceilSqrt_eq,
      Nat.cast_mul, Nat.cast_ofNat]
  have hm : repairWindowMean 2 m = ((m : ℚ) / 2 : ℚ) := by
    norm_num [repairWindowMean]
  rw [repairWindowDegree, repairWindowUpper, repairWindowLower, hm, hr]
  simp only [clockDegree, r, ← Rat.cast_natCast (α := ℝ), ← Rat.cast_add, ← Rat.cast_sub,
    Rat.ceil_cast, Rat.floor_cast]

/-- Exponent of the least binary clock period covering the interpolation degree. -/
def clockExponent (m : ℕ) : ℕ := Nat.clog 2 (max 2 (clockDegree m))

theorem clockExponent_eq (m : ℕ) :
    clockExponent m = Nat.clog 2 (max 2 (repairWindowDegree 2 m)) := by
  rw [clockExponent, clockDegree_eq]

theorem degree_le_clockPeriod (m : ℕ) : repairWindowDegree 2 m ≤ 2 ^ clockExponent m := by
  rw [clockExponent_eq]
  exact (le_max_right _ _).trans (Nat.le_pow_clog (by decide) _)

/-- One extension exponent supplies roots for both the clock and the check nodes. -/
def extensionExponent (d W : ℕ) : ℕ := max d (Nat.clog 2 W)

theorem extensionExponent_clock (d W : ℕ) : d ≤ extensionExponent d W + 1 :=
  (le_max_left _ _).trans (Nat.le_succ _)

theorem extensionExponent_nodes (d W : ℕ) : W ≤ 2 ^ (extensionExponent d W + 1) :=
  (Nat.le_pow_clog (by decide) W).trans
    (Nat.pow_le_pow_right (by decide) ((le_max_right d _).trans (Nat.le_succ _)))

end PencilSearch

end NearSquareRoot
end Computability
end OAI
