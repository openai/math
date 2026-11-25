import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! # Separating distinct semiring evaluations

A rational threshold between the two values of a separating tensor can be
expressed using natural-number constants in the semiring. Adding one to
each side makes both tensors strictly positive at every normalized point.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped NNReal
section

private theorem exists_nat_threshold {x y : ℝ≥0} (h : x < y) :
    ∃ n m : ℕ, x * n < m ∧ (m : ℝ≥0) < y * n := by
  have hxy : (x : ℝ) < (y : ℝ) := h
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ((y : ℝ) - x))
  have hgap := (div_lt_iff₀ (sub_pos.mpr hxy)).mp hn
  let m := ⌊(x : ℝ) * n⌋₊ + 1
  have hl : (x : ℝ) * n < m := by
    simpa [m] using Nat.lt_floor_add_one ((x : ℝ) * n)
  have hr : (m : ℝ) < (y : ℝ) * n := by
    simp only [m, Nat.cast_add, Nat.cast_one]
    linarith only [Nat.floor_le (show 0 ≤ (x : ℝ) * n by positivity), hgap]
  exact ⟨n, m, by exact_mod_cast hl, by exact_mod_cast hr⟩

private theorem opposing_of_lt {S : Type*} [Semiring S] (f g : S →+* ℝ≥0)
    {x : S} (h : f x < g x) :
    ∃ B C : S, f B < f C ∧ g C < g B ∧ ∀ e : S →+* ℝ≥0, 0 < e B ∧ 0 < e C := by
  obtain ⟨n, m, hf, hg⟩ := exists_nat_threshold h
  refine ⟨x * n + 1, (m : S) + 1, ?_, ?_, ?_⟩
  · simpa using hf
  · simpa using hg
  · intro e
    simp only [map_add, map_mul, map_natCast, map_one]
    exact ⟨by positivity, by positivity⟩

/-- Two different normalized semiring homomorphisms order some pair of
tensors oppositely, with both evaluations positive everywhere. -/
theorem exists_opposing_evaluations {S : Type*} [Semiring S] (f g : S →+* ℝ≥0)
    (hne : f ≠ g) :
    ∃ B C : S, f B < f C ∧ g C < g B ∧ ∀ e : S →+* ℝ≥0, 0 < e B ∧ 0 < e C := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ g x := by
    by_contra! hall
    exact hne (RingHom.ext hall)
  rcases lt_or_gt_of_ne hx with hf | hg
  · exact opposing_of_lt f g hf
  · obtain ⟨B, C, h₁, h₂, hp⟩ := opposing_of_lt g f hg
    exact ⟨C, B, h₂, h₁, fun e => (hp e).symm⟩

end

end SpectralBooks
end LinearAlgebra
end OAI
