import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The rational inequalities used to extend the answers to all minor indices in one run
of the compression algorithm (§3). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- Saturation of a logarithmic comparison at magnitude `B`. -/
def clip (B x : ℝ) : ℝ := max (-B) (min x B)

theorem abs_clip_sub_clip_le (B x y : ℝ) : |clip B x - clip B y| ≤ |x - y| := by
  calc
    _ ≤ |min x B - min y B| := by
      simpa [clip, max_comm] using abs_max_sub_max_le_abs (min x B) (min y B) (-B)
    _ ≤ _ := by
      simpa using abs_min_sub_min_le_max x B y B

/-- A closed half-line or interval with rational endpoints.
Each such constraint on a rational affine expression gives at most two rational inequalities. -/
inductive ClipRow where
  | lower (lo : ℚ)
  | upper (hi : ℚ)
  | interval (lo hi : ℚ)
  deriving DecidableEq

def ClipRow.Holds (row : ClipRow) (x : ℝ) : Prop :=
  match row with
  | .lower lo => lo ≤ x
  | .upper hi => x ≤ hi
  | .interval lo hi => (lo : ℝ) ≤ x ∧ x ≤ hi

/-- Round towards minus infinity on the rational grid with spacing `η`. -/
noncomputable def gridFloor (η : ℚ) (v : ℝ) : ℚ :=
  (⌊v / (η : ℝ)⌋ : ℚ) * η

theorem gridFloor_bounds {η : ℚ} (hη : 0 < η) (v : ℝ) :
    (gridFloor η v : ℝ) ≤ v ∧ v < (gridFloor η v : ℝ) + η := by
  have h : (0 : ℝ) < η := by exact_mod_cast hη
  have h₁ := (le_div_iff₀ h).mp (Int.floor_le (v / (η : ℝ)))
  have h₂ := (div_lt_iff₀ h).mp (Int.lt_floor_add_one (v / (η : ℝ)))
  simp only [gridFloor, Rat.cast_mul, Rat.cast_intCast, add_mul, one_mul] at *
  exact ⟨h₁, h₂⟩

/-- The constraint chosen from the true (generally irrational) logarithmic comparison. -/
noncomputable def comparisonRow (B η : ℚ) (v : ℝ) : ClipRow :=
  if (B : ℝ) ≤ v then .lower (B - 16 * η)
  else if v ≤ -(B : ℝ) then .upper (-B + 16 * η)
  else .interval (gridFloor η v - 16 * η) (gridFloor η v + 16 * η)

theorem comparisonRow_holds_of_close {B η : ℚ} (hη : 0 < η) {v w : ℝ}
    (hvw : |w - v| ≤ 8 * (η : ℝ)) : (comparisonRow B η v).Holds w := by
  have hη' : 0 < (η : ℝ) := by exact_mod_cast hη
  have hw := abs_le.mp hvw
  have hg := gridFloor_bounds hη v
  unfold comparisonRow
  split
  · simp only [ClipRow.Holds, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
    linarith
  · split
    · simp only [ClipRow.Holds, Rat.cast_add, Rat.cast_neg, Rat.cast_mul, Rat.cast_ofNat]
      linarith
    · simp only [ClipRow.Holds, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
      constructor <;> linarith

theorem comparisonRow_abs_clip_sub_le {B η : ℚ} (hB : 0 ≤ B) (hη : 0 < η) {v w : ℝ}
    (hw : (comparisonRow B η v).Holds w) : |clip (B : ℝ) w - clip B v| ≤ 17 * (η : ℝ) := by
  have hB' : 0 ≤ (B : ℝ) := by exact_mod_cast hB
  have hη' : 0 < (η : ℝ) := by exact_mod_cast hη
  unfold comparisonRow at hw
  split at hw
  · rename_i hv
    simp only [ClipRow.Holds, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat] at hw
    have hc : clip B v = B := by
      simp only [clip, min_eq_right hv, max_eq_right (by linarith : -(B : ℝ) ≤ B)]
    rw [hc]
    have hlow : (B : ℝ) - 16 * η ≤ clip B w :=
      (le_min hw (by linarith)).trans (le_max_right _ _)
    have hhi : clip B w ≤ B := max_le (by linarith) (min_le_right _ _)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · split at hw
    · rename_i hv
      simp only [ClipRow.Holds, Rat.cast_add, Rat.cast_neg, Rat.cast_mul, Rat.cast_ofNat] at hw
      have hc : clip B v = -(B : ℝ) :=
        max_eq_left ((min_le_left _ _).trans hv)
      rw [hc]
      have hlow : -(B : ℝ) ≤ clip B w := le_max_left _ _
      have hhi : clip B w ≤ -(B : ℝ) + 16 * η :=
        max_le (by linarith) ((min_le_left _ _).trans hw)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · simp only [ClipRow.Holds, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] at hw
      have hg := gridFloor_bounds hη v
      exact (abs_clip_sub_clip_le _ _ _).trans (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- Integer logarithmic comparisons. A four-term comparison may repeat a minor. -/
def intForm {ι : Type*} [Fintype ι] (a : ι → ℤ) (v : ι → ℝ) : ℝ :=
  ∑ i, (a i : ℝ) * v i

theorem intForm_error_le {ι : Type*} [Fintype ι] (a : ι → ℤ) {v w : ι → ℝ} {e : ℝ}
    (h : ∀ i, |v i - w i| ≤ e) :
    |intForm a v - intForm a w| ≤ (∑ i, |(a i : ℝ)|) * e := by
  rw [intForm, intForm, ← Finset.sum_sub_distrib, Finset.sum_mul]
  calc
    _ ≤ ∑ i, |(a i : ℝ) * v i - a i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)

/-- The complete family of rational affine representations of the minor proxies.
The list of generators can be smaller than the type of all minor indices. -/
structure AffineFamily (ι κ : Type*) where
  coefficient : ι → κ → ℚ
  offset : ι → ℚ

def AffineFamily.eval {ι κ : Type*} [Fintype κ] (F : AffineFamily ι κ) (y : κ → ℝ) (u : ι) : ℝ :=
  (∑ j, (F.coefficient u j : ℝ) * y j) + F.offset u

def AffineFamily.evalRat {ι κ : Type*} [Fintype κ] (F : AffineFamily ι κ) (y : κ → ℚ) (u : ι) : ℚ :=
  (∑ j, F.coefficient u j * y j) + F.offset u

theorem AffineFamily.cast_evalRat {ι κ : Type*} [Fintype κ] (F : AffineFamily ι κ)
    (y : κ → ℚ) (u : ι) : (F.evalRat y u : ℝ) = F.eval (fun j => (y j : ℝ)) u := by
  simp [AffineFamily.evalRat, AffineFamily.eval]

/-- Feasibility of all the clipping rows at the original generator proxies. -/
theorem affineFamily_comparisonRows_feasible {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : AffineFamily ι κ) (y : κ → ℝ) (proxy trueLog : ι → ℝ)
    (B η : ℚ) (hη : 0 < η) (hF : ∀ u, |F.eval y u - proxy u| ≤ (η : ℝ))
    (hl : ∀ u, |proxy u - trueLog u| ≤ (η : ℝ))
    (a : ι → ℤ) (ha : ∑ i, |(a i : ℝ)| ≤ 4) :
    (comparisonRow B η (intForm a trueLog)).Holds (intForm a (F.eval y)) := by
  apply comparisonRow_holds_of_close hη
  have h : ∀ u, |F.eval y u - trueLog u| ≤ 2 * (η : ℝ) := fun u =>
    (abs_sub_le _ (proxy u) _).trans (by linarith [hF u, hl u])
  exact (intForm_error_le a h).trans (by
    have hη' : (0 : ℝ) ≤ η := by exact_mod_cast hη.le
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) hη'])

/-- At one rational solution of the rows every minor has a simultaneous rational
assignment. Coordinates used by an answered request have their committed values. -/
theorem affineFamily_common_extension {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : AffineFamily ι κ) (y : κ → ℚ) (trueLog : ι → ℝ) (B η : ℚ)
    (hB : 0 ≤ B) (hη : 0 < η) (answered : Set ι) (reply : ι → ℚ)
    (hy : ∀ u ∈ answered, F.evalRat y u = reply u)
    (hrows : ∀ a : ι → ℤ, (∑ i, |(a i : ℝ)|) ≤ 4 →
      (comparisonRow B η (intForm a trueLog)).Holds
        (intForm a (F.eval fun j => (y j : ℝ)))) :
    ∃ f : ι → ℚ, (∀ u ∈ answered, f u = reply u) ∧
      ∀ a : ι → ℤ, (∑ i, |(a i : ℝ)|) ≤ 4 →
        |clip B (intForm a (fun i => (f i : ℝ))) - clip B (intForm a trueLog)| ≤ 17 * (η : ℝ) := by
  refine ⟨F.evalRat y, hy, fun a ha => ?_⟩
  simp only [AffineFamily.cast_evalRat]
  exact comparisonRow_abs_clip_sub_le hB hη (hrows a ha)

end Compression
end LinearProgramming
end Optimization
end OAI
