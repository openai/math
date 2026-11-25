import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Representatives of price-comparison cells (Section 7) -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning

open Finset

/-- The closed rational constraint for a comparison of an integral feature. -/
def tightenedCut (side : Ordering) (θ x : ℚ) : Prop :=
  match side with
  | .lt => x ≤ (⌈θ⌉ - 1 : ℤ)
  | .eq => x = θ ∧ θ = (⌊θ⌋ : ℤ)
  | .gt => (⌊θ⌋ + 1 : ℤ) ≤ x

theorem tightenedCut_sound (side : Ordering) (θ x : ℚ) (hx : tightenedCut side θ x) :
    compare x θ = side := by
  cases side with
  | lt =>
    apply compare_lt_iff_lt.mpr
    exact lt_of_le_of_lt hx (Int.lt_ceil.mp (by omega : ⌈θ⌉ - 1 < ⌈θ⌉))
  | eq => exact compare_eq_iff_eq.mpr hx.1
  | gt =>
    apply compare_gt_iff_gt.mpr
    exact lt_of_lt_of_le (Int.floor_lt.mp (by omega : ⌊θ⌋ < ⌊θ⌋ + 1)) hx

theorem tightenedCut_int_iff (side : Ordering) (θ : ℚ) (x : ℤ) :
    tightenedCut side θ (x : ℚ) ↔ compare (x : ℚ) θ = side := by
  refine ⟨tightenedCut_sound _ _ _, ?_⟩
  intro h
  cases side with
  | lt =>
    have hlt : x < ⌈θ⌉ := Int.lt_ceil.mpr (compare_lt_iff_lt.mp h)
    change (x : ℚ) ≤ ((⌈θ⌉ - 1 : ℤ) : ℚ)
    exact_mod_cast (show x ≤ ⌈θ⌉ - 1 by omega)
  | eq =>
    have he := compare_eq_iff_eq.mp h
    subst θ
    simp [tightenedCut]
  | gt =>
    have hgt : ⌊θ⌋ < x := Int.floor_lt.mpr (compare_gt_iff_gt.mp h)
    change ((⌊θ⌋ + 1 : ℤ) : ℚ) ≤ (x : ℚ)
    exact_mod_cast (show ⌊θ⌋ + 1 ≤ x by omega)

/-- Rounding potentials down preserves every integer difference bound. -/
theorem floor_difference {x y : ℝ} {c : ℤ} (h : y - x ≤ c) :
    ⌊y⌋ - ⌊x⌋ ≤ c := by
  have h' : y ≤ x + c := by linarith
  have hm := Int.floor_le_floor h'
  rw [Int.floor_add_intCast] at hm
  omega

theorem real_feasible_iff_integer {ι : Type*} (anchor : ι) (arcs : ι → ι → ℤ → Prop) :
    (∃ x : ι → ℝ, x anchor = 0 ∧ ∀ i j c, arcs i j c → x j - x i ≤ c) ↔
      ∃ v : ι → ℤ, v anchor = 0 ∧ ∀ i j c, arcs i j c → v j - v i ≤ c := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨fun i => ⌊x i⌋, by simp [hx], fun i j c hArc => floor_difference (h i j c hArc)⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨fun i => (v i : ℝ), by simp [hv], fun i j c hArc => by dsimp only; exact_mod_cast h i j c hArc⟩

/-- The shortest-path potential from `s`, normalized at the dummy vertex `a`. -/
def potential {ι : Type*} (d : ι → ι → ℤ) (a s i : ι) : ℤ := d s i - d s a

/-- Average of the integer potentials from each source. -/
def representative {p : ℕ} (d : Fin (p+1) → Fin (p+1) → ℤ) (a i : Fin (p+1)) : ℚ :=
  (∑ s, (potential d a s i : ℚ)) / (p + 1 : ℕ)

section Distances

variable {p : ℕ} {d : Fin (p+1) → Fin (p+1) → ℤ}

lemma potential_difference (a i j s : Fin (p+1)) :
    potential d a s i - potential d a s j = d s i - d s j := by
  simp only [potential]; ring

lemma potential_bounds (hTri : ∀ s i j, d s j ≤ d s i + d i j) (a i j s : Fin (p+1)) :
    -(d i j) ≤ potential d a s i - potential d a s j ∧
    potential d a s i - potential d a s j ≤ d j i := by
  rw [potential_difference]
  constructor <;> linarith [hTri s i j, hTri s j i]

lemma potential_extremes (hDiag : ∀ i, d i i = 0) (a i j : Fin (p+1)) :
    potential d a i i - potential d a i j = -(d i j) ∧
    potential d a j i - potential d a j j = d j i := by
  simp [potential_difference, hDiag]

lemma representative_anchor (a : Fin (p+1)) : representative d a a = 0 := by
  simp [representative, potential]

lemma representative_difference (a i j : Fin (p+1)) :
    representative d a i - representative d a j =
      (∑ s, ((potential d a s i - potential d a s j : ℤ) : ℚ)) / (p + 1 : ℕ) := by
  simp [representative, Int.cast_sub, sum_sub_distrib, sub_div]

/-- Each extreme occurs at least once among the summands of the average. -/
theorem average_extremes (f : Fin (p+1) → ℚ) (l u : ℚ)
    (h : ∀ s, l ≤ f s ∧ f s ≤ u) {i j : Fin (p+1)} (hi : f i = l) (hj : f j = u) :
    (u-l) / (p + 1 : ℕ) ≤ (∑ s, f s) / (p + 1 : ℕ) - l ∧
    (u-l) / (p + 1 : ℕ) ≤ u - (∑ s, f s) / (p + 1 : ℕ) := by
  have hL := single_le_sum (f := fun s => f s - l)
    (fun s (_ : s ∈ (univ : Finset (Fin (p+1)))) => sub_nonneg.mpr (h s).1) (mem_univ j)
  have hU := single_le_sum (f := fun s => u - f s)
    (fun s (_ : s ∈ (univ : Finset (Fin (p+1)))) => sub_nonneg.mpr (h s).2) (mem_univ i)
  simp only [hj, hi, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hL hU
  have hp : 0 < ((p+1 : ℕ) : ℚ) := by positivity
  constructor <;> field_simp <;> nlinarith

/-- The feature-margin inequality (7.1). -/
theorem representative_feature_margin
    (hDiag : ∀ i, d i i = 0) (hTri : ∀ s i j, d s j ≤ d s i + d i j)
    (a i j : Fin (p+1)) :
    ((d j i : ℚ) - -(d i j : ℚ)) / (p + 1 : ℕ) ≤
      min ((representative d a i - representative d a j) - -(d i j : ℚ))
        ((d j i : ℚ) - (representative d a i - representative d a j)) := by
  let f (s : Fin (p+1)) : ℚ := (potential d a s i - potential d a s j : ℤ)
  have bounds (s) : -(d i j : ℚ) ≤ f s ∧ f s ≤ (d j i : ℚ) := by
    obtain ⟨h1,h2⟩ := potential_bounds hTri a i j s
    dsimp only [f]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  obtain ⟨hl,hj⟩ := potential_extremes hDiag a i j
  have hl' : f i = -(d i j : ℚ) := by dsimp only [f]; exact_mod_cast hl
  have hj' : f j = (d j i : ℚ) := by dsimp only [f]; exact_mod_cast hj
  rw [representative_difference]
  exact le_min (average_extremes f _ _ bounds hl' hj').1 (average_extremes f _ _ bounds hl' hj').2

end Distances

/-- Disagreement shrinks the range of a feature even when one reported comparison is a tie. -/
theorem exceptional_width {l u l' u' center truth θ k : ℚ}
    (hull : l ≤ l' ∧ l' ≤ u' ∧ u' ≤ u) (hk : 1 ≤ k)
    (margin : (u-l)/k ≤ min (center-l) (u-center))
    (hl : compare l' θ = compare truth θ) (hu : compare u' θ = compare truth θ)
    (different : compare center θ ≠ compare truth θ) :
    u'-l' ≤ (1-1/k)*(u-l) := by
  have low := le_trans margin (min_le_left _ _)
  have high := le_trans margin (min_le_right _ _)
  have width : 0 ≤ u-l := by linarith [hull.1,hull.2.1,hull.2.2]
  have factor : 0 ≤ 1 - 1/k := sub_nonneg.mpr ((div_le_one (by linarith : 0 < k)).mpr hk)
  have hr : (1 - 1/k)*(u-l) = (u-l) - (u-l)/k := by ring
  cases h : compare truth θ with
  | lt =>
    have hu' := compare_lt_iff_lt.mp (hu.trans h)
    have hc : θ ≤ center := le_of_not_gt fun hc => different ((compare_lt_iff_lt.mpr hc).trans h.symm)
    rw [hr]; linarith [hull.1]
  | eq =>
    have hl' := compare_eq_iff_eq.mp (hl.trans h)
    have hu' := compare_eq_iff_eq.mp (hu.trans h)
    rw [hl', hu', sub_self]; exact mul_nonneg factor width
  | gt =>
    have hl' := compare_gt_iff_gt.mp (hl.trans h)
    have hc : center ≤ θ := le_of_not_gt fun hc => different ((compare_gt_iff_gt.mpr hc).trans h.symm)
    rw [hr]; linarith [hull.2.2]

end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
