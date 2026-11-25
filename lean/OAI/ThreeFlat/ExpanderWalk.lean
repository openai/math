import OAI.Computability.VPVNP.Barycenter
import OAI.ThreeFlat.ExpanderCesaroMatrix

namespace OAI
/-! # The variance of a stationary walk under barycentric smoothing -/

noncomputable section
namespace ThreeFlat.Expander

open Finset Matrix Computability.VPVNP.SpectralGeometry

variable {V X : Type*} [Fintype V] [DecidableEq V] [PseudoMetricSpace X]

variable [CompleteSpace X] [Nonempty X] (hX : HasCATZeroSegments X)
    {A : Matrix V V ℝ} (hA : A ∈ rowStochastic ℝ V)

private def smooth (x : V → X) (i : V) : X :=
  (exists_barycenter_variance hX (A i) x (fun j => hA.1 i j)
    (sum_row_of_mem_rowStochastic hA i)).choose

private theorem smooth_spec (x : V → X) (i : V) (z : X) :
    (∑ j, A i j * dist (smooth hX hA x i) (x j)^2) +
      dist (smooth hX hA x i) z ^ 2 ≤ ∑ j, A i j * dist (x j) z ^ 2 := by
  have h := (exists_barycenter_variance hX (A i) x (fun j => hA.1 i j)
    (sum_row_of_mem_rowStochastic hA i)).choose_spec z
  simpa only [weightedSquaredDistance, smooth, dist_comm _ (Classical.choose _)] using h

def walkPlacement (x : V → X) : ℕ → V → X
  | 0 => x
  | n+1 => smooth hX hA (walkPlacement x n)

def walkError (x : V → X) (n : ℕ) (i : V) : ℝ :=
  ∑ j, A i j * dist (walkPlacement hX hA x (n+1) i) (walkPlacement hX hA x n j)^2

/-- The conditional squared-distance loss already accumulated on arriving at
each vertex after `n` applications of the barycentric update. -/
private def accumulated (x : V → X) : ℕ → V → ℝ
  | 0 => 0
  | n+1 => walkError hX hA x n + A *ᵥ accumulated x n

private theorem conditional_distance (x : V → X) (h : ℕ) (z : X) (i : V) :
    dist (walkPlacement hX hA x h i) z ^ 2 + accumulated hX hA x h i ≤
      ((A ^ h) *ᵥ (fun j => dist (x j) z ^ 2)) i := by
  induction h generalizing i with
  | zero => simp [walkPlacement, accumulated]
  | succ n ih =>
    rw [pow_succ' A n, ← mulVec_mulVec]
    have hb := smooth_spec hX hA (walkPlacement hX hA x n) i z
    change walkError hX hA x n i + dist (walkPlacement hX hA x (n+1) i) z^2 ≤ _ at hb
    have hc := sum_le_sum (s := (univ : Finset V)) fun j _ =>
      mul_le_mul_of_nonneg_left (ih j) (hA.1 i j)
    simp only [mul_add, sum_add_distrib] at hc
    change _ + (walkError hX hA x n i + ∑ j, A i j * accumulated hX hA x n j) ≤
      ∑ j, A i j * _ at ⊢
    linarith only [hb, hc]

theorem walk_distance_add_errors_le_energy (hcol : A ∈ colStochastic ℝ V)
    (x : V → X) (h : ℕ) :
    avg (fun i => dist (x i) (walkPlacement hX hA x h i)^2) +
      ∑ n ∈ range h, avg (walkError hX hA x n) ≤ energy (A^h) x := by
  have total (n : ℕ) :
      avg (accumulated hX hA x n) = ∑ g ∈ range n, avg (walkError hX hA x g) := by
    induction n with
    | zero => simp [accumulated, avg]
    | succ n ih =>
      rw [sum_range_succ, ← ih]
      change avg (fun i => walkError hX hA x n i + (A *ᵥ accumulated hX hA x n) i) = _
      rw [avg_add, add_comm]
      congr 1
      unfold avg
      rw [sum_mulVec_of_mem_colStochastic hcol]
  rw [← total, ← avg_add]
  apply avg_le
  intro i
  simpa only [mulVec, dotProduct, dist_comm _ (x i)] using
    conditional_distance hX hA x h (x i) i

end ThreeFlat.Expander

end
end OAI
