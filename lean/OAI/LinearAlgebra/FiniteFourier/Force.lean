import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Tactic

/-!
# First-phase forces of a weighted swap

Positions and forces are ordered by input labels `A,B` and output labels
`A',B'`. A normalized force has been divided by the common leg capacity
`m = log₂ N`. The saturation and disk arguments use only real Euclidean
geometry and the two force properties of grouped, contracted tensors.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A force gives a linear lower bound on the price at every placement. -/
def IsNormalizedForce (m : ℝ) (price : (Fin 4 → E) → ℝ) (g : Fin 4 → E) : Prop :=
  ∀ x, m * (∑ i, ⟪g i, x i⟫_ℝ) ≤ price x

/-- The normalized rank-disk condition on the partial sums `0,u,v` of
the forces in a three-site grouping. -/
def InDiameterOneDisk (u v : E) : Prop :=
  ∃ c : E, ‖c‖ ≤ 1 / 2 ∧ ‖u - c‖ ≤ 1 / 2 ∧ ‖v - c‖ ≤ 1 / 2

private theorem half_eq_of_sum_unit {u v : E} (hu : ‖u‖ ≤ 1 / 2) (hv : ‖v‖ ≤ 1 / 2)
    (hsum : ‖u + v‖ = 1) : u = v := by
  have htri := norm_add_le u v
  exact eq_of_norm_eq_of_norm_add_eq (by linarith) (by linarith)

/-- A diameter-one disk through both `0` and a unit vector `u` must
be centered at `u/2`. -/
theorem InDiameterOneDisk.dist_half_le {u v : E} (h : InDiameterOneDisk u v)
    (hu : ‖u‖ = 1) : ‖v - (1 / 2 : ℝ) • u‖ ≤ 1 / 2 := by
  obtain ⟨c, hc, huc, hvc⟩ := h
  have hc' := half_eq_of_sum_unit hc huc (by simpa using hu)
  have heq : c = (1 / 2 : ℝ) • u := by
    calc
      c = (1 / 2 : ℝ) • (c + c) := by module
      _ = (1 / 2 : ℝ) • u := by
        conv_lhs => arg 2; right; rw [hc']
        simp
  simpa only [← heq] using hvc

/-- The internal forces of both phase tensors coincide with `(p+r)/2`.
The first disk is the grouping `A,A',(B,B')`, and the second is the grouping
`B',B,(A,A')`. -/
theorem internal_forces_eq_half {p r a b : E} (hp : ‖p‖ = 1) (hr : ‖r‖ = 1)
    (hsum : a + b = p + r) (h₁ : InDiameterOneDisk p (p - a))
    (h₂ : InDiameterOneDisk (-p) (b - p)) :
    a = (1 / 2 : ℝ) • (p + r) ∧ b = (1 / 2 : ℝ) • (p + r) := by
  have ha := h₁.dist_half_le hp
  have hb := h₂.dist_half_le (by simpa using hp)
  rw [show p - a - (1 / 2 : ℝ) • p = -(a - (1 / 2 : ℝ) • p) by module, norm_neg] at ha
  rw [show b - p - (1 / 2 : ℝ) • (-p) = b - (1 / 2 : ℝ) • p by module] at hb
  have hab := half_eq_of_sum_unit ha hb (by
    rw [show a - (1 / 2 : ℝ) • p + (b - (1 / 2 : ℝ) • p) = (a + b) - p by module, hsum]
    simpa using hr)
  have heq : a = b := by simpa only [sub_left_inj] using hab
  subst b
  have half : a = (1 / 2 : ℝ) • (p + r) := by rw [← hsum]; module
  exact ⟨half, half⟩

/-- Each one of the four boundary forces in a saturated weighted swap must
point in the assigned unit direction. -/
theorem boundary_force_eq_of_saturated {g d : Fin 4 → E}
    (hg : ∀ i, ‖g i‖ ≤ 1) (hd : ∀ i, ‖d i‖ = 1)
    (hs : 4 ≤ ∑ i, ⟪g i, d i⟫_ℝ) : g = d := by
  have hle i : ⟪g i, d i⟫_ℝ ≤ 1 := by
    simpa [hd i] using (real_inner_le_norm (g i) (d i)).trans (mul_le_mul_of_nonneg_right
      (hg i) (norm_nonneg (d i)))
  funext i
  have heq : ⟪g i, d i⟫_ℝ = 1 := by
    have hpos j : 0 ≤ 1 - ⟪g j, d j⟫_ℝ := sub_nonneg.mpr (hle j)
    have hsingle := Finset.single_le_sum (f := fun j ↦ 1 - ⟪g j, d j⟫_ℝ)
      (fun j _ ↦ hpos j) (Finset.mem_univ i)
    rw [Finset.sum_sub_distrib] at hsingle
    simp at hsingle
    linarith [hle i]
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have h := norm_sub_sq_real (g i) (d i)
  rw [hd i, heq] at h
  nlinarith [sq_le_sq₀ (norm_nonneg (g i)) zero_le_one |>.mpr (hg i),
    norm_nonneg (g i - d i)]

/-- Extract the normalized force of the first phase in an exact weighted
swap construction. The two force hypotheses are the contraction-lifting
and grouped rank-disk properties (CD, Lemmas 5.1 and 5.2). -/
theorem first_phase_force_of_weighted_swap {m : ℝ} (hm : 0 < m)
    {price swapPrice : (Fin 4 → E) → ℝ} {p r : E} (hp : ‖p‖ = 1) (hr : ‖r‖ = 1)
    (hprice : 4 * m ≤ swapPrice ![p, r, -r, -p])
    (hattain : ∃ g : Fin 4 → E, (∀ i, ‖g i‖ ≤ 1) ∧
      m * (∑ i, ⟪g i, (![p, r, -r, -p] : Fin 4 → E) i⟫_ℝ) =
        swapPrice ![p, r, -r, -p] ∧ IsNormalizedForce m swapPrice g)
    (hlift : ∀ g : Fin 4 → E, IsNormalizedForce m swapPrice g →
      ∃ a b : E, IsNormalizedForce m price ![g 0, g 1, -a, -b] ∧ a + b = g 0 + g 1 ∧
        InDiameterOneDisk (g 0) (g 0 - a) ∧ InDiameterOneDisk (g 3) (b + g 3)) :
    IsNormalizedForce m price
      ![p, r, -((1 / 2 : ℝ) • (p + r)), -((1 / 2 : ℝ) • (p + r))] := by
  obtain ⟨g, hg, hval, hforce⟩ := hattain
  let d : Fin 4 → E := ![p, r, -r, -p]
  have hd : ∀ i, ‖d i‖ = 1 := by intro i; fin_cases i <;> simp [d, hp, hr]
  have heq : g = d := boundary_force_eq_of_saturated hg hd (by
    change 4 ≤ ∑ i, ⟪g i, (![p, r, -r, -p] : Fin 4 → E) i⟫_ℝ
    nlinarith)
  obtain ⟨a, b, h, hs, h₁, h₂⟩ := hlift g hforce
  subst g
  change IsNormalizedForce m price ![p, r, -a, -b] at h
  change a + b = p + r at hs
  change InDiameterOneDisk p (p - a) at h₁
  change InDiameterOneDisk (-p) (b + -p) at h₂
  obtain ⟨ha, hb⟩ := internal_forces_eq_half hp hr hs h₁ (by simpa [sub_eq_add_neg] using h₂)
  simpa [ha, hb] using h

end FiniteFourier
end LinearAlgebra
end OAI
