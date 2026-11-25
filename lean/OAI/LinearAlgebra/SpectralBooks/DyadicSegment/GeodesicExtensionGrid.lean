import OAI.Geometry.HyperbolicGroups.Basic

/-! # Dyadic subdivision by exact midpoints

At level `n` the chain has `2 ^ n` edges of equal length. Its total
length equals the distance between its endpoints, so every subchain
also realizes the distance between its endpoints.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace DyadicSegment

variable {X : Type*}

/-- The dyadic subdivision of the segment from `x` to `y` using `mid`.
The indices of level `n` range from zero to `2 ^ n`, inclusive. -/
def grid (mid : X → X → X) (x y : X) : ℕ → ℕ → X
  | 0, k => if k = 0 then x else y
  | n + 1, k => if k % 2 = 0 then grid mid x y n (k / 2)
    else mid (grid mid x y n (k / 2)) (grid mid x y n (k / 2 + 1))

theorem grid_even (mid : X → X → X) (x y : X) (n k : ℕ) :
    grid mid x y (n + 1) (2 * k) = grid mid x y n k := by
  simp [grid]

theorem grid_odd (mid : X → X → X) (x y : X) (n k : ℕ) :
    grid mid x y (n + 1) (2 * k + 1) =
      mid (grid mid x y n k) (grid mid x y n (k + 1)) := by
  simp [grid, show (2 * k + 1) / 2 = k by omega,
    show (2 * k + 1) % 2 = 1 by omega]

theorem grid_zero (mid : X → X → X) (x y : X) (n : ℕ) :
    grid mid x y n 0 = x := by
  induction n with
  | zero => simp [grid]
  | succ n ih => simpa using (grid_even mid x y n 0).trans ih

theorem grid_last (mid : X → X → X) (x y : X) (n : ℕ) :
    grid mid x y n (2 ^ n) = y := by
  induction n with
  | zero => simp [grid]
  | succ n ih => rwa [pow_succ', grid_even]

variable [MetricSpace X]

theorem grid_adjacent (mid : X → X → X)
    (hm : ∀ a b, dist a (mid a b) = dist a b / 2 ∧ dist (mid a b) b = dist a b / 2)
    (x y : X) (n k : ℕ) (hk : k < 2 ^ n) :
    dist (grid mid x y n k) (grid mid x y n (k + 1)) = dist x y / 2 ^ n := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by simpa using hk
    simp [this, grid]
  | succ n ih =>
    rw [pow_succ'] at hk
    let j := k / 2
    have hj : j < 2 ^ n := by dsimp [j]; omega
    have cases : k = 2 * j ∨ k = 2 * j + 1 := by dsimp [j]; omega
    have half : dist x y / 2 ^ n / 2 = dist x y / 2 ^ (n + 1) := by
      rw [pow_succ, div_div]
    rcases cases with he | ho
    · rw [he, grid_even, grid_odd, (hm _ _).1, ih _ hj, half]
    · rw [ho, show 2 * j + 1 + 1 = 2 * (j + 1) by omega,
        grid_odd, grid_even, (hm _ _).2, ih _ hj, half]

private theorem chain_dist_le (p : ℕ → X) (N : ℕ) (δ : ℝ)
    (h : ∀ k < N, dist (p k) (p (k + 1)) ≤ δ) (k l : ℕ) (hkl : k ≤ l) (hl : l ≤ N) :
    dist (p k) (p l) ≤ ((l : ℝ) - k) * δ := by
  induction l, hkl using Nat.le_induction with
  | base => simp
  | succ l hkl ih =>
    have h₁ := ih (by omega)
    have h₂ := h l (by omega)
    have h₃ := dist_triangle (p k) (p l) (p (l + 1))
    push_cast
    linarith

/-- Distances within one dyadic subdivision have the exact linear formula. -/
theorem grid_dist (mid : X → X → X)
    (hm : ∀ a b, dist a (mid a b) = dist a b / 2 ∧ dist (mid a b) b = dist a b / 2)
    (x y : X) (n k l : ℕ) (hkl : k ≤ l) (hl : l ≤ 2 ^ n) :
    dist (grid mid x y n k) (grid mid x y n l) = ((l : ℝ) - k) / 2 ^ n * dist x y := by
  let p := grid mid x y n
  let N := 2 ^ n
  let δ := dist x y / 2 ^ n
  have bound := chain_dist_le p N δ (fun i hi => (grid_adjacent mid hm x y n i hi).le)
  have full : (N : ℝ) * δ = dist x y := by
    dsimp [N, δ]
    push_cast
    field_simp
  have ends : dist (p 0) (p N) = dist x y := by
    simp only [p, N, grid_zero, grid_last]
  have h₁ := bound 0 k (Nat.zero_le _) (hkl.trans hl)
  have h₂ := bound l N hl le_rfl
  have h₃ := dist_triangle (p 0) (p k) (p N)
  have h₄ := dist_triangle (p k) (p l) (p N)
  rw [ends] at h₃
  simp only [Nat.cast_zero, sub_zero] at h₁
  change dist (p k) (p l) = _
  rw [show ((l : ℝ) - k) / 2 ^ n * dist x y = ((l : ℝ) - k) * δ by dsimp [δ]; ring]
  exact le_antisymm (bound k l hkl hl) (by linarith)

end DyadicSegment

end SpectralBooks
end LinearAlgebra
end OAI
