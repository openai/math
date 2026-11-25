import OAI.LinearAlgebra.FiniteFourier.ForceLift
import OAI.LinearAlgebra.FiniteFourier.LongMove

/-! # The first force of an exact two-phase weighted swap

The rank bounds for the two three-site groupings enter only as semiperimeter
inequalities. They give the diameter-disk restrictions on the internal
forces directly by testing a remote placement in the saturated direction.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Saturated boundary forces and the two grouped semiperimeter bounds
determine the internal forces. This formulation also applies after passing
to the limit in a sequence of phase constructions. -/
theorem internal_eq_of_grouped_bounds {m : ℝ} (hm : 0 < m) {p r a b : E}
    (hp : ‖p‖ = 1) (hr : ‖r‖ = 1)
    (hfirst : ∀ A U A' : E,
      m * (⟪p,A⟫_ℝ + ⟪r,U⟫_ℝ + ⟪-a,A'⟫_ℝ + ⟪-b,U⟫_ℝ) ≤
      m / 2 * (‖A-A'‖ + ‖A'-U‖ + ‖U-A‖))
    (hsecond : ∀ B U B' : E,
      m * (⟪a,U⟫_ℝ + ⟪b,B⟫_ℝ + ⟪-r,U⟫_ℝ + ⟪-p,B'⟫_ℝ) ≤
      m / 2 * (‖B'-B‖ + ‖B-U‖ + ‖U-B'‖)) :
    a = (1 / 2 : ℝ) • (p + r) ∧ b = (1 / 2 : ℝ) • (p + r) := by
  have hbalance : a + b = p + r := by
    let v := p + r - (a + b)
    have h : ⟪v,v⟫_ℝ ≤ 0 := by
      have hh := hfirst v v v
      simp only [sub_self, norm_zero, add_zero, mul_zero, inner_neg_left] at hh
      change ⟪p + r - (a + b),v⟫_ℝ ≤ 0
      simp only [inner_sub_left, inner_add_left]
      nlinarith only [hh, hm]
    have hv : p + r - (a + b) = 0 := by
      apply (@inner_self_eq_zero ℝ E _ _ _ _).mp
      exact le_antisymm h real_inner_self_nonneg
    exact (sub_eq_zero.mp hv).symm
  have ha := force_mem_diameter_disk_of_semiperimeter p a hp (by
    intro R hR v
    have h := hfirst (R • p) 0 (-v)
    simp only [inner_zero_right, inner_neg_left, inner_neg_right, neg_neg, add_zero,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hp, one_pow, mul_one, sub_neg_eq_add,
      sub_zero, norm_neg, zero_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at h
    nlinarith only [h, hm])
  have hb := force_mem_diameter_disk_of_semiperimeter p b hp (by
    intro R hR v
    have h := hsecond v 0 (-(R • p))
    rw [show -(R • p) - v = -(R • p + v) by abel] at h
    simp only [inner_zero_right, inner_neg_left, inner_neg_right, neg_neg, zero_add, add_zero,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hp, one_pow, mul_one, sub_zero,
      norm_neg, zero_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at h
    nlinarith only [h, hm])
  have hhalf : ‖(1 / 2 : ℝ) • p‖ ≤ 1 / 2 := by simp [norm_smul, hp]
  apply internal_forces_eq_half hp hr hbalance
  · refine ⟨(1 / 2 : ℝ) • p, hhalf, ?_, ?_⟩
    · rwa [show p - (1 / 2 : ℝ) • p = (1 / 2 : ℝ) • p by module]
    · rwa [show p - a - (1 / 2 : ℝ) • p = -(a - (1 / 2 : ℝ) • p) by module, norm_neg]
  · refine ⟨-((1 / 2 : ℝ) • p), by simpa using hhalf, ?_, ?_⟩
    · rwa [show -p - -((1 / 2 : ℝ) • p) = -((1 / 2 : ℝ) • p) by module, norm_neg]
    · rwa [show b - p - -((1 / 2 : ℝ) • p) = b - (1 / 2 : ℝ) • p by module]

/-- Exact weighted-swap case of the first-phase force extraction. The hypotheses
are the price of the weighted swap, the single-leg movement bound, the contraction
price bound, and the two three-legged rank bounds written as triangle prices. -/
theorem exact_swap_first_phase_force [FiniteDimensional ℝ E] {m : ℝ} (hm : 0 < m)
    {T H D : (Fin 4 → E) → ℝ} (hT : SublinearPrice T) (hH : SublinearPrice H)
    (hD : SublinearPrice D) (hleg : ∀ i v, T (Pi.single i v) ≤ m * ‖v‖)
    (hwire : ∀ A B U V C F, T ![A,B,C,F] ≤ H ![A,B,U,V] + D ![U,V,C,F])
    (h₁ : ∀ A U A' : E, H ![A,U,A',U] ≤ m / 2 * (‖A-A'‖ + ‖A'-U‖ + ‖U-A‖))
    (h₂ : ∀ B U B' : E, D ![U,B,U,B'] ≤ m / 2 * (‖B'-B‖ + ‖B-U‖ + ‖U-B'‖))
    {p r : E} (hp : ‖p‖ = 1) (hr : ‖r‖ = 1) (hswap : 4 * m ≤ T ![p,r,-r,-p]) :
    IsNormalizedForce m H
      ![p,r,-((1 / 2 : ℝ) • (p + r)),-((1 / 2 : ℝ) • (p + r))] := by
  let u : Fin 4 → E := ![p,r,-r,-p]
  have hne : u ≠ 0 := by
    intro hu
    have hp0 : p = 0 := congrFun hu 0
    simp [hp0] at hp
  obtain ⟨g, hg, hv, hf⟩ := exists_attaining_normalized_force hT hm hleg hne
  have hd i : ‖u i‖ = 1 := by fin_cases i <;> simp [u, hp, hr]
  have hmatch : g = u := boundary_force_eq_of_saturated hg hd (by
    change 4 * m ≤ T u at hswap
    nlinarith)
  obtain ⟨a,b,hA,hB⟩ := lift_two_phase_force hm hH hD hwire hf
  subst g
  have hfirst (A U A' : E) := (hA ![A,U,A',U]).trans (h₁ A U A')
  have hsecond (B U B' : E) := (hB ![U,B,U,B']).trans (h₂ B U B')
  simp only [Fin.sum_univ_four] at hfirst hsecond
  obtain ⟨ha,hb⟩ := internal_eq_of_grouped_bounds hm hp hr hfirst hsecond
  change IsNormalizedForce m H ![p,r,-a,-b] at hA
  simpa only [ha,hb] using hA

end FiniteFourier
end LinearAlgebra
end OAI
