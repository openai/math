import OAI.LinearAlgebra.FiniteFourier.Force
import Mathlib

/-! # Moving the two input legs of the first phase to infinity -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

open Filter
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The first-order distance correction when the input leg moves out along a unit ray. -/
theorem tendsto_norm_longMove_sub (p X : E) (hp : ‖p‖ = 1) :
    Tendsto (fun R : ℝ ↦ ‖R • p - X‖ - R) atTop (𝓝 (-⟪p, X⟫)) := by
  have hi : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hd : Tendsto (fun R : ℝ ↦ ‖p - R⁻¹ • X‖ + 1) atTop (𝓝 (1 + 1 : ℝ)) := by
    simpa [hp] using ((tendsto_const_nhds.sub (hi.smul_const X)).norm.add_const 1 :
      Tendsto (fun R : ℝ ↦ ‖p - R⁻¹ • X‖ + 1) atTop (𝓝 (‖p - (0 : ℝ) • X‖ + 1)))
  have hn : Tendsto (fun R : ℝ ↦ R⁻¹ * ‖X‖ ^ 2 - 2 * ⟪p, X⟫) atTop (𝓝 (-2 * ⟪p, X⟫)) := by
    simpa using (hi.mul_const (‖X‖ ^ 2)).sub_const (2 * ⟪p, X⟫)
  have hlim := hn.div hd (by norm_num)
  convert hlim.congr' _ using 1
  · simp; ring
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hnorm : ‖p - R⁻¹ • X‖ = R⁻¹ * ‖R • p - X‖ := by
    have hh : p - R⁻¹ • X = R⁻¹ • (R • p - X) := by
      rw [smul_sub, inv_smul_smul₀ hR.ne']
    rw [hh, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  have hnorm2 := norm_sub_sq_real (R • p) X
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, hp, mul_one, real_inner_smul_left] at hnorm2
  have hdpos : 0 < ‖p - R⁻¹ • X‖ + 1 := by positivity
  simp only [Pi.div_apply]
  rw [div_eq_iff hdpos.ne', hnorm]
  field_simp
  nlinarith

/-- Doubling the total copying cost and subtracting the leading `4R` isolates its
finite correction at the original four sites. -/
private theorem tendsto_longMove_cost (p r A B A' B' : E) (hp : ‖p‖ = 1) (hr : ‖r‖ = 1) :
    Tendsto (fun R : ℝ ↦
      (‖R • p - A‖ - R) + (‖R • p - A'‖ - R) - ‖A - A'‖ +
      (‖R • r - B‖ - R) + (‖R • r - B'‖ - R) - ‖B - B'‖) atTop
      (𝓝 (-⟪p,A⟫ + -⟪p,A'⟫ - ‖A-A'‖ + -⟪r,B⟫ + -⟪r,B'⟫ - ‖B-B'‖)) :=
  (((((tendsto_norm_longMove_sub p A hp).add
    (tendsto_norm_longMove_sub p A' hp)).sub_const _).add
      (tendsto_norm_longMove_sub r B hr)).add (tendsto_norm_longMove_sub r B' hr)).sub_const _

private theorem exists_unit_direction [Nontrivial E] (x : E) :
    ∃ p : E, ‖p‖ = 1 ∧ ⟪p, x⟫ = ‖x‖ := by
  by_cases hx : x = 0
  · obtain ⟨y, hy⟩ := exists_ne (0 : E)
    exact ⟨NormedSpace.normalize y, NormedSpace.norm_normalize hy, by simp [hx]⟩
  · exact ⟨NormedSpace.normalize x, NormedSpace.norm_normalize hx, by
      simp [NormedSpace.normalize, real_inner_smul_left,
        sq, norm_ne_zero_iff.mpr hx]⟩

omit [InnerProductSpace ℝ E] in
/-- Apply the three-site copying estimate first to the repeated first index
and then to the repeated second index. -/
theorem two_input_copy_bound (P : (Fin 4 → E) → ℝ) (m : ℝ) (A B A' B' : E)
    (h₁ : ∀ x, P ![x, B, A', B'] ≤ P ![A, B, A', B'] +
      m / 2 * (‖x - A‖ + ‖x - A'‖ - ‖A - A'‖))
    (h₂ : ∀ x y, P ![x, y, A', B'] ≤ P ![x, B, A', B'] +
      m / 2 * (‖y - B‖ + ‖y - B'‖ - ‖B - B'‖)) (x y : E) :
    P ![x, y, A', B'] ≤ P ![A, B, A', B'] + m / 2 *
      (‖x - A‖ + ‖x - A'‖ - ‖A - A'‖ + ‖y - B‖ + ‖y - B'‖ - ‖B - B'‖) := by
  linarith only [h₁ x, h₂ x y]

/-- The long-move implication in the price-forced-by-a-swap proposition. The
force bound may use a different sequence of first matrices for each pair of
unit directions. The `price` can thus be the supremum of the family prices. -/
theorem fourLeg_lowerBound_of_force_and_copy [Nontrivial E] (m : ℝ)
    (price : (Fin 4 → E) → ℝ) (A B A' B' : E)
    (force : ∀ p r : E, ‖p‖ = 1 → ‖r‖ = 1 → ∀ R : ℝ, 0 < R →
      m * (2 * R - (1 / 2 : ℝ) * ⟪p + r, A' + B'⟫) ≤ price ![R • p, R • r, A', B'])
    (copy : ∀ x y : E, price ![x, y, A', B'] ≤ price ![A, B, A', B'] + m / 2 *
      (‖x-A‖ + ‖x-A'‖ - ‖A-A'‖ + ‖y-B‖ + ‖y-B'‖ - ‖B-B'‖)) :
    m / 2 * (‖A-A'‖ + ‖B-B'‖ + ‖A-B'‖ + ‖B-A'‖) ≤ price ![A,B,A',B'] := by
  obtain ⟨p, hp, hpX⟩ := exists_unit_direction (A - B')
  obtain ⟨r, hr, hrX⟩ := exists_unit_direction (B - A')
  have hl := ((tendsto_longMove_cost p r A B A' B' hp hr).const_mul (m / 2)).add_const
    (price ![A, B, A', B'])
  have hh := ge_of_tendsto hl (b := - (m / 2) * ⟪p + r, A' + B'⟫) (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have h := (force p r hp hr R hR).trans (copy (R • p) (R • r))
    change - (m / 2) * ⟪p + r, A' + B'⟫ ≤ _
    linarith only [h])
  rw [inner_sub_right] at hpX hrX
  simp only [inner_add_left, inner_add_right] at hh
  rw [← hpX, ← hrX]
  linarith only [hh]

/-- The four-leg lower bound for a family, from the limiting normalized force
and the pointwise copying bound. Only the original-placement family price
needs a finite upper bound. -/
theorem family_fourLeg_lowerBound [Nontrivial E] {ι : Type*} [Nonempty ι]
    (m : ℝ) (P : ι → (Fin 4 → E) → ℝ) (A B A' B' : E)
    (hb : BddAbove (Set.range fun j ↦ P j ![A, B, A', B']))
    (hforce : ∀ p r : E, ‖p‖ = 1 → ‖r‖ = 1 →
      IsNormalizedForce m (fun x ↦ ⨆ j, P j x)
        ![p, r, -((1 / 2 : ℝ) • (p+r)), -((1 / 2 : ℝ) • (p+r))])
    (hcopy : ∀ j (x y : E), P j ![x, y, A', B'] ≤ P j ![A, B, A', B'] + m / 2 *
      (‖x-A‖ + ‖x-A'‖ - ‖A-A'‖ + ‖y-B‖ + ‖y-B'‖ - ‖B-B'‖)) :
    m / 2 * (‖A-A'‖ + ‖B-B'‖ + ‖A-B'‖ + ‖B-A'‖) ≤ ⨆ j, P j ![A,B,A',B'] := by
  apply fourLeg_lowerBound_of_force_and_copy m (fun x ↦ ⨆ j, P j x)
  · intro p r hp hr R _
    have h := hforce p r hp hr ![R • p, R • r, A', B']
    rw [Fin.sum_univ_four] at h
    change m * (⟪p, R • p⟫ + ⟪r, R • r⟫ + ⟪-((1 / 2 : ℝ) • (p + r)), A'⟫ +
      ⟪-((1 / 2 : ℝ) • (p + r)), B'⟫) ≤ _ at h
    simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, hp, hr, one_pow,
      mul_one, inner_neg_left, real_inner_smul_left] at h
    rw [inner_add_right]
    linarith only [h]
  · intro x y
    exact ciSup_le fun j ↦ (hcopy j x y).trans (add_le_add_left (le_ciSup hb j) _)

/-- A limiting force of family members bounds the supremum of their prices,
even when the selected matrices depend on the approaching sequence. -/
theorem family_isNormalizedForce_of_tendsto {ι κ : Type*} {l : Filter κ} [l.NeBot]
    {m : ℝ} (P : ι → (Fin 4 → E) → ℝ) (hb : ∀ x, BddAbove (Set.range fun j ↦ P j x))
    (j : κ → ι) (g : κ → Fin 4 → E) (G : Fin 4 → E)
    (hforce : ∀ᶠ k in l, IsNormalizedForce m (P (j k)) (g k))
    (hg : ∀ i, Tendsto (fun k ↦ g k i) l (𝓝 (G i))) :
    IsNormalizedForce m (fun x ↦ ⨆ i, P i x) G := by
  intro x
  apply le_of_tendsto (tendsto_const_nhds.mul (tendsto_finsetSum _ fun i _ ↦
    (hg i).inner tendsto_const_nhds))
  filter_upwards [hforce] with k hk
  exact (hk x).trans (le_ciSup (hb x) (j k))

/-- A semiperimeter upper bound and a unit boundary force place the next
partial sum in the disk having diameter `[0,p]`. -/
theorem force_mem_diameter_disk_of_semiperimeter (p a : E) (hp : ‖p‖ = 1)
    (h : ∀ (R : ℝ), 0 < R → ∀ v : E,
      R + ⟪a, v⟫ ≤ (‖R • p + v‖ + ‖v‖ + R) / 2) :
    ‖a - (1 / 2 : ℝ) • p‖ ≤ 1 / 2 := by
  let v := a - (1 / 2 : ℝ) • p
  have hlim := (tendsto_norm_longMove_sub p (-v) hp).add_const ‖v‖
  have hbound := ge_of_tendsto hlim (b := 2 * ⟪a, v⟫) (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    simp only [sub_neg_eq_add]
    linarith only [h R hR v])
  simp only [inner_neg_right, neg_neg] at hbound
  have hsq : ‖v‖ ^ 2 = ⟪a, v⟫ - (1/2 : ℝ) * ⟪p, v⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => lhs; unfold v
    rw [inner_sub_left, real_inner_smul_left]
  change ‖v‖ ≤ 1 / 2
  nlinarith

end

end FiniteFourier
end LinearAlgebra
end OAI
