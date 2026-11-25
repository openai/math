import OAI.ThreeFlat.ExpanderBasic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Linarith

namespace OAI
/-! # Quadratic Poincaré estimates for clouds connected by a matching -/

namespace ThreeFlat.Expander

open Finset
open scoped BigOperators
variable {V P X : Type*} [Fintype V] [Fintype P] [PseudoMetricSpace X]

/-- The mean energy of the copies of the inner graph. -/
noncomputable def internalEnergy (H : Matrix P P ℝ) (x : V × P → X) : ℝ :=
  avg fun u => energy H (fun p => x (u,p))

/-- Mean energy of one outgoing matching arc per port. -/
noncomputable def matchingEnergy {W : Type*} [Fintype W] (e : Equiv.Perm W)
    (x : W → X) : ℝ := avg fun i => dist (x i) (x (e i)) ^ 2

private theorem dist_sq_three (a b c d : X) :
    dist a d ^ 2 ≤ 3 * (dist a b ^ 2 + dist b c ^ 2 + dist d c ^ 2) := by
  have h := dist_triangle4 a b c d
  rw [dist_comm c d] at h
  have hs := pow_le_pow_left₀ dist_nonneg h 2
  nlinarith [sq_nonneg (dist a b - dist b c), sq_nonneg (dist b c - dist d c),
    sq_nonneg (dist d c - dist a b)]

theorem variance_le_via_placement [Nonempty V] (f g : V → X) :
    variance f ≤ 3 * (2 * avg (fun i => dist (f i) (g i) ^ 2) + variance g) := by
  calc
    _ ≤ avg (fun i => avg (fun j => 3 * (dist (f i) (g i)^2 +
        dist (g i) (g j)^2 + dist (f j) (g j)^2))) :=
      avg_le fun i => avg_le fun j => dist_sq_three ..
    _ = _ := by
      simp_rw [avg_mul, avg_add, avg_const]
      unfold variance
      ring

theorem matchingEnergy_le_via_placement {W : Type*} [Fintype W]
    (e : Equiv.Perm W) (f g : W → X) :
    matchingEnergy e g ≤ 3 * (2 * avg (fun i => dist (f i) (g i)^2) + matchingEnergy e f) := by
  let r (i : W) := dist (f i) (g i)^2
  calc
    _ ≤ avg (fun i => 3 * (r i + dist (f i) (f (e i))^2 + (r ∘ e) i)) := by
      apply avg_le
      intro i
      simpa only [r, Function.comp_apply, dist_comm (g i) (f i),
        dist_comm (g (e i)) (f (e i))] using dist_sq_three (g i) (f i) (f (e i)) (g (e i))
    _ = _ := by
      rw [avg_mul, avg_add, avg_add, avg_equiv e r]
      change 3 * (avg r + matchingEnergy e f + avg r) = 3 * (2 * avg r + matchingEnergy e f)
      ring

private theorem average_fst [Nonempty P] (f : V → ℝ) :
    avg (fun i : V × P => f i.1) = avg f := by
  rw [avg_prod (fun u (_ : P) => f u)]
  simp

@[simp] theorem variance_cloud_projection [Nonempty P] (y : V → X) :
    variance (fun i : V × P => y i.1) = variance y := by
  calc
    _ = avg (fun i : V × P => avg (fun j : V => dist (y i.1) (y j)^2)) :=
      avg_congr _ _ fun i => average_fst (P := P) (fun j : V => dist (y i.1) (y j)^2)
    _ = _ := average_fst (P := P) (fun i : V => avg (fun j => dist (y i) (y j)^2))

/-- Choosing the best member of each cloud as its center bounds the mean
squared radius by the inner energy times the inner Poincaré constant. -/
theorem exists_cloud_center [Nonempty P] (H : Matrix P P ℝ) {β : ℝ} (hH : Bound H X β)
    (x : V × P → X) :
    ∃ y : V → X, avg (fun i => dist (x i) (y i.1)^2) ≤ β * internalEnergy H x := by
  let cost (u : V) (p : P) : ℝ := avg (fun j => dist (x (u,p)) (x (u,j))^2)
  choose p hp using (fun u => Finite.exists_min (cost u))
  refine ⟨fun u => x (u,p u), ?_⟩
  rw [avg_prod (fun u j => dist (x (u,j)) (x (u,p u))^2), internalEnergy, ← avg_mul]
  apply avg_le
  intro u
  have hmin : cost u (p u) ≤ avg (cost u) := by
    rw [← avg_const (V := P) (cost u (p u))]
    exact avg_le fun j => hp u j
  calc
    _ = cost u (p u) := avg_congr _ _ fun j => by rw [dist_comm]
    _ ≤ _ := hmin.trans (hH (fun j => x (u,j)))

/-- Comparison for a replacement step. The outer inequality measures each
matching edge at its two cloud centers. -/
theorem cloud_variance_le [Nonempty V] [Nonempty P] (H : Matrix P P ℝ)
    (e : Equiv.Perm (V × P)) {β γ : ℝ} (hγ : 0 ≤ γ) (hH : Bound H X β)
    (houter : ∀ y : V → X, variance y ≤ γ * matchingEnergy e (fun i => y i.1))
    (x : V × P → X) :
    variance x ≤ (6 + 18 * γ) * β * internalEnergy H x + 9 * γ * matchingEnergy e x := by
  obtain ⟨y, hcenter⟩ := exists_cloud_center H hH x
  have hv := variance_le_via_placement x (fun i => y i.1)
  rw [variance_cloud_projection] at hv
  have hm := matchingEnergy_le_via_placement e x (fun i => y i.1)
  have hy := (houter y).trans (mul_le_mul_of_nonneg_left hm hγ)
  have hscaled := mul_le_mul_of_nonneg_left hcenter (show 0 ≤ 6 + 18 * γ by positivity)
  linarith

end ThreeFlat.Expander

end OAI
