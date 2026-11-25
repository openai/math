import OAI.Geometry.HyperbolicGroups.CATZero

namespace OAI
/-! # Orthogonality from equal-radius estimates on the signed axes -/

namespace Hierarchy.AdaptiveProbe
open HyperbolicObstruction
noncomputable section

private theorem inside_axis {X : Type*} [MetricSpace X] (C : CATZero X)
    {A : ℝ → X} (iso : Isometry A) (p : X) (s R d : ℝ) (pos : 0<R) (inside : |s|≤R)
    (left : dist p (A (-R))^2 ≤ R^2+d^2) (right : dist p (A R)^2 ≤ R^2+d^2) :
    dist p (A s)^2 ≤ s^2+d^2 := by
  let q := (s+R)/(2*R)
  have hq : q ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg (by linarith [(abs_le.mp inside).1]) (by positivity),
      (div_le_one (by positivity)).mpr (by linarith [(abs_le.mp inside).2])⟩
  have ratio : q*(2*R)=s+R := div_mul_cancel₀ _ (by positivity)
  have diam : dist (A (-R)) (A R) = 2*R := by
    rw [iso.dist_eq,Real.dist_eq,abs_of_nonpos (by linarith)]
    ring
  have first : dist (A (-R)) (A s) = q*dist (A (-R)) (A R) := by
    rw [diam,ratio,iso.dist_eq,Real.dist_eq,abs_of_nonpos (by linarith [(abs_le.mp inside).1])]
    ring
  have last : dist (A s) (A R)=(1-q)*dist (A (-R)) (A R) := by
    rw [diam,iso.dist_eq,Real.dist_eq,abs_of_nonpos (by linarith [(abs_le.mp inside).2])]
    nlinarith only [ratio]
  have cn := CATZero.cn_of_dist C p hq first last
  rw [diam] at cn
  have bound : dist p (A s)^2 ≤
      (1-q)*(R^2+d^2)+q*(R^2+d^2)-q*(1-q)*(2*R)^2 := by
    linarith only [cn,mul_le_mul_of_nonneg_left left (sub_nonneg.mpr hq.2),
      mul_le_mul_of_nonneg_left right hq.1]
  apply bound.trans_eq
  have es : s=q*(2*R)-R := by linarith only [ratio]
  rw [es]
  ring

/-- The four signed ends at the same radius satisfy the square comparison.
CAT(0) comparison and the opposite pair then give exact distances at all
parameters, without a separate flat-quadrilateral hypothesis. -/
theorem perpendicular_of_equal_radius {X : Type*} [MetricSpace X] (C : CATZero X)
    (A B : ℝ → X) (isoA : Isometry A) (isoB : Isometry B) (origin : A 0=B 0)
    (ends : ∀ s t : ℝ, |s|=|t| → dist (A s) (B t)^2 ≤ s^2+t^2) :
    ∀ s t : ℝ, dist (A s) (B t)^2=s^2+t^2 := by
  have upper (s t : ℝ) : dist (A s) (B t)^2 ≤ s^2+t^2 := by
    rcases le_total |s| |t| with st|ts
    · by_cases z : t=0
      · subst t
        have eq : s=0 := abs_eq_zero.mp (by simpa using le_antisymm st (by simp))
        simp [eq,origin]
      · let R := |t|
        have hl := ends (-R) t (by simp [R])
        have hr := ends R t (by simp [R])
        rw [dist_comm]
        apply inside_axis C isoA (B t) s R t (abs_pos.mpr z) st
        · simpa [dist_comm (B t),sq_abs,R] using hl
        · simpa [dist_comm (B t),sq_abs,R] using hr
    · by_cases z : s=0
      · subst s
        have eq : t=0 := abs_eq_zero.mp (by simpa using le_antisymm ts (by simp))
        simp [eq,origin]
      · let R := |s|
        have hl := ends s (-R) (by simp [R])
        have hr := ends s R (by simp [R])
        rw [add_comm (s^2) (t^2)]
        apply inside_axis C isoB (A s) t R s (abs_pos.mpr z) ts
        · simpa [R,sq_abs] using hl
        · simpa [R,sq_abs] using hr
  intro s t
  apply le_antisymm (upper s t)
  have diam : dist (A (-s)) (A s)=2*|s| := by
    rw [isoA.dist_eq,Real.dist_eq,show -s-s = -(2*s) by ring,abs_neg, abs_mul]
    norm_num
  have h₁ : dist (A (-s)) (A 0)=(1/2:ℝ)*dist (A (-s)) (A s) := by rw [diam,isoA.dist_eq]; simp []
  have h₂ : dist (A 0) (A s)=(1-1/2:ℝ)*dist (A (-s)) (A s) := by
    rw [diam,isoA.dist_eq]
    simp only [Real.dist_eq,zero_sub,abs_neg]
    ring
  have mid := CATZero.cn_of_dist C (B t) (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1) h₁ h₂
  rw [origin,isoB.dist_eq,Real.dist_eq,sub_zero,sq_abs,diam,dist_comm (B t) (A s),
    dist_comm (B t) (A (-s)),mul_pow,sq_abs] at mid
  nlinarith only [mid,upper (-s) t]

end
end Hierarchy.AdaptiveProbe

end OAI
