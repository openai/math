import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Projective
import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Growth
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Positive weighted averages of a projective orbit

These elementary finite identities supply the approximate eigenvectors used in
the compactness argument. Every average is a convex combination of actual
members of the invariant set. No fixed-point theorem is assumed here.
-/

noncomputable section

namespace OAI.LinearAlgebra.TensorSpectrum

open scoped BigOperators
open Set

variable {S : Type*} [CommMonoidWithZero S]

/-- Iteration of the normalized multiplication map, starting at `f₀`. -/
def projectiveOrbit (z : S) (f₀ : S → ℝ) : ℕ → S → ℝ
  | 0 => f₀
  | n + 1 => projective z (projectiveOrbit z f₀ n)

/-- The unnormalized mass of the `n`th translated function. -/
def projectiveMass (z : S) (f₀ : S → ℝ) (n : ℕ) : ℝ := f₀ (z ^ n)

theorem projectiveOrbit_mem (K : Set (S → ℝ)) (z : S) (f₀ : S → ℝ)
    (hf₀ : f₀ ∈ K) (hinvariant : MapsTo (projective z) K K) (n : ℕ) :
    projectiveOrbit z f₀ n ∈ K := by
  induction n with
  | zero => exact hf₀
  | succ n ih => exact hinvariant ih

/-- Undoing all normalizations in the orbit gives the original translate. -/
theorem projectiveOrbit_normalized (z : S) (f₀ : S → ℝ)
    (hunit : f₀ 1 = 1)
    (hz : ∀ n, projectiveOrbit z f₀ n z ≠ 0) (n : ℕ) (x : S) :
    f₀ (z ^ n * x) = projectiveMass z f₀ n * projectiveOrbit z f₀ n x := by
  induction n generalizing x with
  | zero => simp [projectiveMass, projectiveOrbit, hunit]
  | succ n ih =>
    have hm : projectiveMass z f₀ (n + 1) =
        projectiveMass z f₀ n * projectiveOrbit z f₀ n z := by
      simpa only [projectiveMass, pow_succ] using ih z
    calc
      f₀ (z ^ (n + 1) * x) = f₀ (z ^ n * (z * x)) := by
        rw [pow_succ, mul_assoc]
      _ = projectiveMass z f₀ n * projectiveOrbit z f₀ n (z * x) := ih (z * x)
      _ = projectiveMass z f₀ (n + 1) *
          (projectiveOrbit z f₀ n (z * x) / projectiveOrbit z f₀ n z) := by
        rw [hm]
        field_simp [hz n]
      _ = projectiveMass z f₀ (n + 1) * projectiveOrbit z f₀ (n + 1) x := rfl

theorem projectiveMass_succ (z : S) (f₀ : S → ℝ) (hunit : f₀ 1 = 1)
    (hz : ∀ n, projectiveOrbit z f₀ n z ≠ 0) (n : ℕ) :
    projectiveMass z f₀ (n + 1) =
      projectiveMass z f₀ n * projectiveOrbit z f₀ n z := by
  simpa only [projectiveMass, pow_succ] using
    projectiveOrbit_normalized z f₀ hunit hz n z

theorem projectiveMass_one_le (K : Set (S → ℝ)) (z : S) (f₀ : S → ℝ)
    (hf₀ : f₀ ∈ K) (hunit : f₀ 1 = 1)
    (hlower : ∀ f ∈ K, 1 ≤ f z)
    (hinvariant : MapsTo (projective z) K K) (n : ℕ) :
    1 ≤ projectiveMass z f₀ n := by
  have ho : ∀ k, 1 ≤ projectiveOrbit z f₀ k z := fun k =>
    hlower _ (projectiveOrbit_mem K z f₀ hf₀ hinvariant k)
  have hz : ∀ k, projectiveOrbit z f₀ k z ≠ 0 := fun k =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (ho k))
  induction n with
  | zero => simp [projectiveMass, hunit]
  | succ n ih =>
    rw [projectiveMass_succ z f₀ hunit hz n]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ projectiveMass z f₀ n * projectiveOrbit z f₀ n z :=
        mul_le_mul ih (ho n) zero_le_one (le_trans zero_le_one ih)

theorem projectiveMass_le_pow (K : Set (S → ℝ)) (z : S) (f₀ : S → ℝ)
    (hf₀ : f₀ ∈ K) (hunit : f₀ 1 = 1)
    (hlower : ∀ f ∈ K, 1 ≤ f z)
    (hinvariant : MapsTo (projective z) K K)
    (M : ℝ) (hupper : ∀ f ∈ K, f z ≤ M) (n : ℕ) :
    projectiveMass z f₀ n ≤ M ^ n := by
  have ho : ∀ k, 1 ≤ projectiveOrbit z f₀ k z := fun k =>
    hlower _ (projectiveOrbit_mem K z f₀ hf₀ hinvariant k)
  have hz : ∀ k, projectiveOrbit z f₀ k z ≠ 0 := fun k =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (ho k))
  have hM : 0 ≤ M := le_trans zero_le_one (le_trans (hlower f₀ hf₀) (hupper f₀ hf₀))
  induction n with
  | zero => simp [projectiveMass, hunit]
  | succ n ih =>
    rw [projectiveMass_succ z f₀ hunit hz n, pow_succ]
    exact mul_le_mul ih
      (hupper _ (projectiveOrbit_mem K z f₀ hf₀ hinvariant n))
      (le_trans zero_le_one (ho n)) (pow_nonneg hM n)

/-- A finite positive weighted mean, with its denominator kept explicit. -/
def positiveWeightedMean (w : ℕ → ℝ) (u : ℕ → S → ℝ) (n : ℕ) : S → ℝ :=
  fun x => (∑ k ∈ Finset.range (n + 1), w k * u k x) /
    (∑ k ∈ Finset.range (n + 1), w k)

theorem positive_weight_sum (w : ℕ → ℝ) (hw : ∀ k, 0 < w k) (n : ℕ) :
    0 < ∑ k ∈ Finset.range (n + 1), w k := by
  induction n with
  | zero => simpa using hw 0
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact add_pos ih (hw (n + 1))

omit [CommMonoidWithZero S] in
/-- Binary convexity suffices for membership of all finite weighted means. -/
theorem positiveWeightedMean_mem (K : Set (S → ℝ)) (hconvex : Convex ℝ K)
    (w : ℕ → ℝ) (u : ℕ → S → ℝ)
    (hw : ∀ k, 0 < w k) (hu : ∀ k, u k ∈ K) (n : ℕ) :
    positiveWeightedMean w u n ∈ K := by
  induction n with
  | zero =>
    have heq : positiveWeightedMean w u 0 = u 0 := by
      funext x
      simp [positiveWeightedMean, ne_of_gt (hw 0)]
    rw [heq]
    exact hu 0
  | succ n ih =>
    let W : ℝ := ∑ k ∈ Finset.range (n + 1), w k
    have hW : 0 < W := positive_weight_sum w hw n
    have hden : 0 < W + w (n + 1) := add_pos hW (hw (n + 1))
    have ha : 0 ≤ W / (W + w (n + 1)) := div_nonneg hW.le hden.le
    have hb : 0 ≤ w (n + 1) / (W + w (n + 1)) :=
      div_nonneg (hw (n + 1)).le hden.le
    have hab : W / (W + w (n + 1)) + w (n + 1) / (W + w (n + 1)) = 1 := by
      rw [← add_div, div_self hden.ne']
    have hmem := hconvex ih (hu (n + 1)) ha hb hab
    have heq : positiveWeightedMean w u (n + 1) =
        (W / (W + w (n + 1))) • positiveWeightedMean w u n +
          (w (n + 1) / (W + w (n + 1))) • u (n + 1) := by
      funext x
      simp only [positiveWeightedMean, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_range_succ (fun k => w k * u k x) (n + 1),
        Finset.sum_range_succ w (n + 1)]
      change ((∑ k ∈ Finset.range (n + 1), w k * u k x) + w (n + 1) * u (n + 1) x) /
          (W + w (n + 1)) =
        (W / (W + w (n + 1))) *
            ((∑ k ∈ Finset.range (n + 1), w k * u k x) / W) +
          (w (n + 1) / (W + w (n + 1))) * u (n + 1) x
      field_simp [hW.ne', hden.ne']
    rw [heq]
    exact hmem

/-- The finite unnormalized power-series sum of the translated coordinates. -/
def projectiveSum (z : S) (f₀ : S → ℝ) (s : ℝ) (n : ℕ) (x : S) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), f₀ (z ^ k * x) / s ^ k

/-- Its normalized mean; its mass denominator is exactly the scalar growth API. -/
def projectiveAverage (z : S) (f₀ : S → ℝ) (s : ℝ) (n : ℕ) : S → ℝ :=
  fun x => projectiveSum z f₀ s n x /
    MultiplicativeGrowth.weightedSum (projectiveMass z f₀) s n

theorem projective_weightedSum_pos (K : Set (S → ℝ)) (z : S) (f₀ : S → ℝ)
    (hf₀ : f₀ ∈ K) (hunit : f₀ 1 = 1)
    (hlower : ∀ f ∈ K, 1 ≤ f z)
    (hinvariant : MapsTo (projective z) K K) (s : ℝ) (hs : 0 < s) (n : ℕ) :
    0 < MultiplicativeGrowth.weightedSum (projectiveMass z f₀) s n := by
  apply positive_weight_sum
  intro k
  exact div_pos
    (lt_of_lt_of_le zero_lt_one (projectiveMass_one_le K z f₀ hf₀ hunit hlower hinvariant k))
    (pow_pos hs k)

theorem projectiveAverage_eq_weightedMean (z : S) (f₀ : S → ℝ)
    (hunit : f₀ 1 = 1) (hz : ∀ n, projectiveOrbit z f₀ n z ≠ 0)
    (s : ℝ) (n : ℕ) :
    projectiveAverage z f₀ s n =
      positiveWeightedMean (fun k => projectiveMass z f₀ k / s ^ k)
        (projectiveOrbit z f₀) n := by
  funext x
  simp only [projectiveAverage, projectiveSum, positiveWeightedMean,
    MultiplicativeGrowth.weightedSum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [projectiveOrbit_normalized z f₀ hunit hz k x]
  ring

theorem projectiveAverage_mem (K : Set (S → ℝ)) (hconvex : Convex ℝ K)
    (z : S) (f₀ : S → ℝ) (hf₀ : f₀ ∈ K) (hunit : f₀ 1 = 1)
    (hlower : ∀ f ∈ K, 1 ≤ f z)
    (hinvariant : MapsTo (projective z) K K) (s : ℝ) (hs : 0 < s) (n : ℕ) :
    projectiveAverage z f₀ s n ∈ K := by
  have hz : ∀ k, projectiveOrbit z f₀ k z ≠ 0 := fun k =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one
      (hlower _ (projectiveOrbit_mem K z f₀ hf₀ hinvariant k)))
  rw [projectiveAverage_eq_weightedMean z f₀ hunit hz s n]
  apply positiveWeightedMean_mem K hconvex
  · intro k
    exact div_pos
      (lt_of_lt_of_le zero_lt_one
        (projectiveMass_one_le K z f₀ hf₀ hunit hlower hinvariant k))
      (pow_pos hs k)
  · exact projectiveOrbit_mem K z f₀ hf₀ hinvariant

theorem projectiveSum_succ (z : S) (f₀ : S → ℝ) (s : ℝ) (n : ℕ) (x : S) :
    projectiveSum z f₀ s (n + 1) x =
      projectiveSum z f₀ s n x + f₀ (z ^ (n + 1) * x) / s ^ (n + 1) := by
  exact Finset.sum_range_succ _ _

/-- The telescoping identity before dividing by the total weight. -/
theorem projectiveSum_residual (z : S) (f₀ : S → ℝ) (s : ℝ) (hs : 0 < s)
    (n : ℕ) (x : S) :
    projectiveSum z f₀ s n (z * x) - s * projectiveSum z f₀ s n x =
      s * (f₀ (z ^ (n + 1) * x) / s ^ (n + 1) - f₀ x) := by
  have hshift (k : ℕ) :
      f₀ (z ^ k * (z * x)) / s ^ k =
        s * (f₀ (z ^ (k + 1) * x) / s ^ (k + 1)) := by
    rw [show z ^ (k + 1) * x = z ^ k * (z * x) by rw [pow_succ, mul_assoc]]
    rw [pow_succ]
    field_simp [hs.ne']
  induction n with
  | zero =>
    simp only [projectiveSum, Finset.sum_range_one, pow_zero, one_mul, div_one,
      zero_add, pow_one]
    field_simp [hs.ne']
  | succ n ih =>
    rw [projectiveSum_succ, projectiveSum_succ]
    have h := hshift (n + 1)
    linarith

/-- The sole boundary terms of the normalized approximate-eigenvector equation. -/
theorem projectiveAverage_residual (z : S) (f₀ : S → ℝ)
    (hunit : f₀ 1 = 1) (hz : ∀ n, projectiveOrbit z f₀ n z ≠ 0)
    (s : ℝ) (hs : 0 < s) (n : ℕ) (x : S) :
    projectiveAverage z f₀ s n (z * x) - s * projectiveAverage z f₀ s n x =
      s * ((projectiveMass z f₀ (n + 1) / s ^ (n + 1) /
          MultiplicativeGrowth.weightedSum (projectiveMass z f₀) s n) *
          projectiveOrbit z f₀ (n + 1) x -
        f₀ x / MultiplicativeGrowth.weightedSum (projectiveMass z f₀) s n) := by
  unfold projectiveAverage
  calc
    projectiveSum z f₀ s n (z * x) /
          MultiplicativeGrowth.weightedSum (projectiveMass z f₀) s n -
        s * (projectiveSum z f₀ s n x /
          MultiplicativeGrowth.weightedSum (projectiveMass z f₀) s n) =
      (projectiveSum z f₀ s n (z * x) - s * projectiveSum z f₀ s n x) /
        MultiplicativeGrowth.weightedSum (projectiveMass z f₀) s n := by ring
    _ = _ := by
      rw [projectiveSum_residual z f₀ s hs n x,
        projectiveOrbit_normalized z f₀ hunit hz (n + 1) x]
      ring

end OAI.LinearAlgebra.TensorSpectrum
