import OAI.HyperbolicObstruction.ParallelSpace

namespace OAI
/-! # Parallel lines through an orthogonal marked axis -/

namespace Hierarchy.AdaptiveProbe
open HyperbolicObstruction
noncomputable section

private theorem coordinate_of_quadratics (a t C : ℝ)
    (h : ∀ u : ℝ, (a-u)^2 ≤ (t-u)^2+C^2) : a=t := by
  by_contra ne
  let v := (C^2+1)/(a-t)
  have hv : v*(a-t)=C^2+1 := div_mul_cancel₀ _ (sub_ne_zero.mpr ne)
  have hu := h (t-v)
  nlinarith [sq_nonneg (a-t),sq_nonneg C]

/-- Every point of the second axis lies on a calibrated line parallel to
the first. Its point at coordinate `s` is the midpoint of the doubled
axis marks. This construction uses CAT(0) squared-distance comparison. -/
theorem parallel_through_orthogonal_axis {X : Type*} [MetricSpace X]
    (C : CATZero X) (A B : ℝ → X) (isoA : Isometry A) (isoB : Isometry B)
    (origin : A 0=B 0) (orth : ∀ u v : ℝ, dist (A u) (B v)^2 = u^2+v^2)
    (b : X → ℝ) (lip : LipschitzWith 1 b) (c : ℝ) (phase : ∀ u, b (A u)=c+u)
    (v : ℝ) :
    ∃ l : ℝ → X, Isometry l ∧ l 0=B v ∧
      (∀ s, b (l s)=c+s) ∧ (∀ s, dist (l s) (A s) ≤ |v|) := by
  let l (s : ℝ) := CATZero.mid C (A (2*s)) (B (2*v))
  have upper (s u : ℝ) : dist (A u) (l s)^2 ≤ (s-u)^2+v^2 := by
    have h := CATZero.mid_cn C (A (2*s)) (B (2*v)) (A u)
    rw [isoA.dist_eq,Real.dist_eq,sq_abs,orth,orth] at h
    nlinarith only [h]
  have right (s : ℝ) : dist (l s) (B (2*v))^2=s^2+v^2 := by
    dsimp only [l]
    rw [CATZero.dist_mid_right, div_pow, orth]
    ring
  have synchronize (s : ℝ) : b (l s) = c+s := by
    have h := coordinate_of_quadratics (b (l s)-c) s v (by
      intro u
      have h₁ := lip.dist_le_mul (l s) (A u)
      simp only [NNReal.coe_one,one_mul] at h₁
      have h₂ := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr h₁
      rw [Real.dist_eq, sq_abs,phase,dist_comm (l s)] at h₂
      nlinarith only [h₂,upper s u])
    linarith
  refine ⟨l,Isometry.of_dist_eq (fun s t => ?_), ?_,synchronize, ?_⟩
  · have lower := lip.dist_le_mul (l s) (l t)
    simp only [NNReal.coe_one,one_mul,synchronize,Real.dist_eq,add_sub_add_left_eq_sub] at lower
    apply le_antisymm _ lower
    apply (sq_le_sq₀ dist_nonneg (abs_nonneg _)).mp
    have h := CATZero.mid_cn C (A (2*t)) (B (2*v)) (l s)
    rw [dist_comm (l s) (A (2*t)),right,orth] at h
    rw [sq_abs]
    nlinarith only [h, upper s (2*t)]
  · dsimp only [l,CATZero.mid]
    rw [mul_zero,origin]
    symm
    apply CATZero.eq_segment_of_dist C (by norm_num)
    · rw [isoB.dist_eq,isoB.dist_eq]
      simp [Real.dist_eq, abs_mul]
    · rw [isoB.dist_eq, isoB.dist_eq]
      simp [Real.dist_eq, show v-2*v = -v by ring, abs_mul]
      ring
  · intro s
    apply (sq_le_sq₀ dist_nonneg (abs_nonneg _)).mp
    simpa only [dist_comm (A s),sub_self,zero_pow (by decide : 2≠0),zero_add,sq_abs] using upper s s

end
end Hierarchy.AdaptiveProbe

end OAI
