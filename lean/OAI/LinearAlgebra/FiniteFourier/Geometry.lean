import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# Spectral prices at rectangle placements

The four sites are the top left, top right, bottom left and bottom right
corners. The row label joins the two left corners and the column label joins
the two right corners. The two-triangle upper bound and the four-leg
first-phase lower bound coincide on every rectangle. Splitting a rectangle
at a collapsed width or height gives the rank and sparsity estimates.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open scoped Classical

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The four-site price for a family of controlled diagonal operators. -/
abbrev PhasePrice (T : Type*) := T → (Fin 4 → Plane) → ℝ

/-- Four corners in the order of the input legs and then their output partners. -/
def rectangleSites (L W : ℝ) : Fin 4 → Plane :=
  ![WithLp.toLp 2 ![-W/2, L/2], WithLp.toLp 2 ![W/2, L/2],
    WithLp.toLp 2 ![-W/2, -L/2], WithLp.toLp 2 ![W/2, -L/2]]

def rectanglePrice {T : Type*} (P : PhasePrice T) (M : T) (L W : ℝ) : ℝ :=
  P M (rectangleSites L W)

/-- Spectral value at the fixed normalized rectangle, including the zero matrix. -/
def rectangleValue {T : Type*} [Zero T] (P : PhasePrice T) (M : T) (s c : ℝ) : ℝ :=
  if M = 0 then 0 else (2 : ℝ) ^ (rectanglePrice P M (2*s) (2*c) / (2*(c+s)))

private def rectangleDiagonal (L W : ℝ) := Real.sqrt (L^2 + W^2)

private theorem plane_dist (a b c d : ℝ) :
    dist (WithLp.toLp 2 ![a,b] : Plane) (WithLp.toLp 2 ![c,d]) =
      Real.sqrt ((a-c)^2 + (b-d)^2) := by
  simp [PiLp.dist_eq_of_L2, Fin.sum_univ_two, Real.dist_eq]

private theorem plane_norm (a b : ℝ) :
    ‖(WithLp.toLp 2 ![a,b] : Plane)‖ = Real.sqrt (a^2 + b^2) := by
  simp [PiLp.norm_eq_of_L2, Fin.sum_univ_two, Real.norm_eq_abs]

theorem rectangleSites_add (L W l w : ℝ) :
    rectangleSites (L+l) (W+w) = rectangleSites L W + rectangleSites l w := by
  funext i
  apply PiLp.ext
  intro j
  fin_cases i <;> fin_cases j <;> simp [rectangleSites] <;> ring

private theorem rectangle_vertical {L : ℝ} (hL : 0 ≤ L) (W : ℝ) :
    dist (rectangleSites L W 0) (rectangleSites L W 2) = L ∧
    dist (rectangleSites L W 1) (rectangleSites L W 3) = L := by
  constructor <;> simp [rectangleSites, plane_dist, show L/2 - -L/2 = L by ring, Real.sqrt_sq hL]

private theorem rectangle_cross (L W : ℝ) :
    dist (rectangleSites L W 0) (rectangleSites L W 3) = rectangleDiagonal L W ∧
    dist (rectangleSites L W 1) (rectangleSites L W 2) = rectangleDiagonal L W := by
  constructor <;> simp [rectangleSites, plane_dist, rectangleDiagonal] <;> congr 1 <;> ring

private theorem rectangle_norm (L W : ℝ) (i : Fin 4) :
    ‖rectangleSites L W i‖ = rectangleDiagonal L W / 2 := by
  have hs : Real.sqrt ((L^2 + W^2) / 4) = rectangleDiagonal L W / 2 := by
    rw [Real.sqrt_div (by positivity)]
    norm_num [rectangleDiagonal]
  rw [← hs]
  fin_cases i
  · exact (plane_norm (-W/2) (L/2)).trans (congrArg Real.sqrt (by ring))
  · exact (plane_norm (W/2) (L/2)).trans (congrArg Real.sqrt (by ring))
  · exact (plane_norm (-W/2) (-L/2)).trans (congrArg Real.sqrt (by ring))
  · exact (plane_norm (W/2) (-L/2)).trans (congrArg Real.sqrt (by ring))

/-- The geometric cost of the two common labels, one on each triangle with
third vertex at the center, gives the common rectangle upper bound. -/
theorem rectanglePrice_le_of_common_labels {T : Type*} {P : PhasePrice T} {M : T} {m L W : ℝ}
    (hL : 0 ≤ L)
    (hcommon : ∀ x : Fin 4 → Plane, P M x ≤ m / 2 *
      (dist (x 0) (x 2) + ‖x 0‖ + ‖x 2‖ + dist (x 1) (x 3) + ‖x 1‖ + ‖x 3‖)) :
    rectanglePrice P M L W ≤ (L + Real.sqrt (L^2 + W^2)) * m := by
  have h := hcommon (rectangleSites L W)
  rw [(rectangle_vertical hL W).1, (rectangle_vertical hL W).2] at h
  simp only [rectangle_norm, rectangleDiagonal] at h
  exact h.trans_eq (by ring)

/-- Equality on every rectangle from the four-leg lower bound and the two
label triangle construction. Degenerate rectangles are included. -/
theorem rectanglePrice_eq_of_four_legs {T : Type*} {P : PhasePrice T} {M : T} {m L W : ℝ}
    (hL : 0 ≤ L)
    (hupper : rectanglePrice P M L W ≤ (L + Real.sqrt (L^2 + W^2)) * m)
    (hfour : ∀ x : Fin 4 → Plane, m / 2 *
      (dist (x 0) (x 2) + dist (x 1) (x 3) + dist (x 0) (x 3) + dist (x 1) (x 2)) ≤ P M x) :
    rectanglePrice P M L W = (L + Real.sqrt (L^2 + W^2)) * m := by
  have h := hfour (rectangleSites L W)
  rw [(rectangle_vertical hL W).1, (rectangle_vertical hL W).2,
    (rectangle_cross L W).1, (rectangle_cross L W).2] at h
  exact le_antisymm hupper (le_of_eq_of_le (by unfold rectangleDiagonal; ring) h)

theorem rectangleValue_log {T : Type*} [Zero T] (P : PhasePrice T) {M : T} (hM : M ≠ 0)
    {s c : ℝ} (hd : 0 < c+s) :
    2*(c+s) * Real.logb 2 (rectangleValue P M s c) = rectanglePrice P M (2*s) (2*c) := by
  rw [rectangleValue, ite_eq_right_iff.mpr (fun h => (hM h).elim), Real.logb_rpow (by norm_num) (by norm_num)]
  field_simp

private theorem sqrt_two_sq (a b : ℝ) :
    Real.sqrt ((2*a)^2 + (2*b)^2) = 2 * Real.sqrt (a^2 + b^2) := by
  rw [show (2*a)^2 + (2*b)^2 = 4 * (a^2 + b^2) by ring, Real.sqrt_mul (by norm_num)]
  norm_num

/-- The normalized value of a phase attaining the rectangle bound. -/
theorem normalized_rectangle_saturation {T : Type*} [Zero T] {P : PhasePrice T} {M : T}
    (hM : M ≠ 0) {s c m : ℝ} (hu : c^2 + s^2 = 1)
    (h : rectanglePrice P M (2*s) (2*c) = (2*s + Real.sqrt ((2*s)^2+(2*c)^2))*m) :
    rectangleValue P M s c = (2:ℝ) ^ ((2 + 2*s)*m / (2*(c+s))) := by
  simp only [rectangleValue, ite_eq_right_iff.mpr (fun h => (hM h).elim), h, sqrt_two_sq, add_comm (s^2) (c^2), hu,
    Real.sqrt_one, mul_one, add_comm (2*s) 2]

/-- Subadditivity of a placed phase price specializes to addition of rectangle dimensions. -/
theorem rectanglePrice_subadd {T : Type*} {P : PhasePrice T} {M : T}
    (hadd : ∀ x y, P M (x+y) ≤ P M x + P M y) (L W l w : ℝ) :
    rectanglePrice P M (L+l) (W+w) ≤ rectanglePrice P M L W + rectanglePrice P M l w := by
  simpa only [rectanglePrice, rectangleSites_add] using
    hadd (rectangleSites L W) (rectangleSites l w)

/-- Splitting off `2t` of the width gives the rank estimate of Proposition
`geo:estimates`. The degenerate rectangle price is supplied by its two-site rank. -/
theorem rectangleValue_rank_bound {T : Type*} [Zero T] {P : PhasePrice T} {M : T}
    (hM : M ≠ 0) {s c t m logRank : ℝ} (hs : 0 < s) (hc : 0 < c) (_ht : t ∈ Set.Icc 0 c)
    (hadd : ∀ x y, P M (x+y) ≤ P M x + P M y)
    (hcommon : ∀ x : Fin 4 → Plane, P M x ≤ m/2 *
      (dist (x 0) (x 2) + ‖x 0‖ + ‖x 2‖ + dist (x 1) (x 3) + ‖x 1‖ + ‖x 3‖))
    (hzero : rectanglePrice P M 0 (2*t) = (2*t)*logRank) :
    2*(c+s) * Real.logb 2 (rectangleValue P M s c) ≤
      2*m*(s + Real.sqrt ((c-t)^2+s^2)) + 2*t*logRank := by
  rw [rectangleValue_log _ hM (add_pos hc hs)]
  have h := rectanglePrice_subadd hadd (2*s) (2*(c-t)) 0 (2*t)
  rw [add_zero, show 2*(c-t) + 2*t = 2*c by ring, hzero] at h
  have hu := rectanglePrice_le_of_common_labels (W := 2*(c-t)) (L := 2*s) (mul_nonneg (by norm_num) hs.le) hcommon
  rw [sqrt_two_sq, add_comm (s^2)] at hu
  nlinarith only [hu, h]

/-- Splitting the rectangle into two collapsed rectangles gives the total
support estimate of Proposition `geo:estimates`. -/
theorem rectangleValue_support_bound {T : Type*} [Zero T] {P : PhasePrice T} {M : T}
    (hM : M ≠ 0) {s c m logSupport : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hadd : ∀ x y, P M (x+y) ≤ P M x + P M y)
    (hrank : rectanglePrice P M 0 (2*c) ≤ 2*c*m)
    (hsupp : rectanglePrice P M (2*s) 0 = 2*s*logSupport) :
    2*(c+s) * Real.logb 2 (rectangleValue P M s c) ≤ 2*c*m + 2*s*logSupport := by
  rw [rectangleValue_log _ hM (add_pos hc hs)]
  have h := rectanglePrice_subadd hadd 0 (2*c) (2*s) 0
  rw [zero_add, add_zero, hsupp] at h
  linarith

/-- Each row contains at most `d` nonzero entries, so the matrix has at
most `N*d` entries on its support. -/
theorem matrix_supportCard_le {I O K : Type*} [Fintype I] [Fintype O] [Zero K]
    (M : Matrix O I K) (d : ℕ)
    (hf : ∀ o, (Finset.univ.filter (fun i ↦ M o i ≠ 0)).card ≤ d) :
    ∑ o, (Finset.univ.filter (fun i ↦ M o i ≠ 0)).card ≤ Fintype.card O * d := by
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset O)) (fun o _ ↦ hf o)

/-- The per-output version of the support estimate, for an `N`-row matrix. -/
theorem rectangleValue_row_bound {I O K : Type*} [Fintype I] [Fintype O] [Semiring K]
    {P : PhasePrice (Matrix O I K)} {M : Matrix O I K} (hM : M ≠ 0)
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c) {d : ℕ}
    (hf : ∀ o, (Finset.univ.filter (fun i ↦ M o i ≠ 0)).card ≤ d)
    (hadd : ∀ x y, P M (x+y) ≤ P M x + P M y)
    (hrank : rectanglePrice P M 0 (2*c) ≤ 2*c*Real.logb 2 (Fintype.card O))
    (hsupp : rectanglePrice P M (2*s) 0 =
      2*s*Real.logb 2 (∑ o, (Finset.univ.filter (fun i ↦ M o i ≠ 0)).card : ℕ)) :
    2*(c+s) * Real.logb 2 (rectangleValue P M s c) ≤
      2*(c+s)*Real.logb 2 (Fintype.card O) + 2*s*Real.logb 2 d := by
  classical
  obtain ⟨o, i, hentry⟩ : ∃ o i, M o i ≠ 0 := by
    by_contra! h
    exact hM (Matrix.ext h)
  have hrpos : 0 < (Finset.univ.filter (fun i ↦ M o i ≠ 0)).card :=
    Finset.card_pos.mpr ⟨i, by simp [hentry]⟩
  have hpos := lt_of_lt_of_le hrpos (Finset.single_le_sum
    (f := fun o ↦ (Finset.univ.filter (fun i ↦ M o i ≠ 0)).card)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ o))
  have hd : 0 < d := hrpos.trans_le (hf o)
  have hn : 0 < Fintype.card O := Fintype.card_pos_iff.mpr ⟨o⟩
  have hu := matrix_supportCard_le M d hf
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
    (Nat.cast_pos.mpr hpos) (Nat.cast_le.mpr hu)
  rw [Nat.cast_mul, Real.logb_mul (by exact_mod_cast hn.ne') (by exact_mod_cast hd.ne')] at hlog
  have h := rectangleValue_support_bound hM hs hc hadd hrank hsupp
  nlinarith only [h, mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*s by positivity)]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
