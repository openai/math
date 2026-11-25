import OAI.Geometry.HyperbolicGroups.ConeData
import OAI.Geometry.HyperbolicGroups.TangentRay

namespace OAI
/-! # Finite oriented column axes from opposite test ports -/

namespace Hierarchy.AdaptiveProbe
open HyperbolicObstruction
noncomputable section

/-- Geodesic parameterizations of the opposite port pairs on one bounded-radius pattern. -/
structure ColumnSegments (I X : Type*) [MetricSpace X] (k : ℕ) (R : ℝ) where
  center : I → X
  axis : I → Fin k → ℝ → X
  starts : ∀ i j, axis i j 0 = center i
  intrinsic : ∀ i j s t, |s|≤R → |t|≤R → dist (axis i j s) (axis i j t) = |s-t|
  bounded : ∀ i j s, dist (center i) (axis i j s) ≤ |s|

variable {I X : Type*} [MetricSpace X] {k : ℕ} {R : ℝ}

private def parameter (R t : ℝ) := (t+R)/(2*R)

private theorem parameter_mem (hR : 0<R) {t : ℝ} (ht : |t|≤R) :
    parameter R t ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨lo,hi⟩ := abs_le.mp ht
  exact ⟨div_nonneg (by linarith) (by positivity), (div_le_one (by positivity)).mpr (by linarith)⟩

/-- A center within radius R of two ports at distance 2R is the exact midpoint. -/
theorem column_of_ports (C : CATZero X) (hR : 0<R) (center : I → X)
    (lo hi : I → Fin k → X) (diam : ∀ i j, dist (lo i j) (hi i j)=2*R)
    (left : ∀ i j, dist (lo i j) (center i)≤R)
    (right : ∀ i j, dist (center i) (hi i j)≤R) :
    ∃ A : ColumnSegments I X k R, A.center = center ∧
      (∀ i j, A.axis i j (-R)=lo i j) ∧ ∀ i j, A.axis i j R=hi i j := by
  let f (i : I) (j : Fin k) (t : ℝ) :=
    if |t|≤R then CATZero.segment C (lo i j) (hi i j) (parameter R t) else center i
  have starts (i : I) (j : Fin k) : f i j 0 = center i := by
    have d := dist_triangle (lo i j) (center i) (hi i j)
    rw [diam] at d
    dsimp only [f]
    rw [ite_eq_left (by simpa using hR.le)]
    symm
    apply CATZero.eq_segment_of_dist C (parameter_mem hR (by simpa using hR.le))
    · rw [diam]
      dsimp [parameter]
      rw [div_mul_cancel₀ _ (by positivity)]
      linarith [left i j,right i j]
    · rw [diam]
      have v : parameter R 0*(2*R) = R := by
        rw [parameter,div_mul_cancel₀ _ (by positivity),zero_add]
      linarith [left i j,right i j]
  have intrinsic (i : I) (j : Fin k) (s t : ℝ) (hs : |s|≤R) (ht : |t|≤R) :
      dist (f i j s) (f i j t)=|s-t| := by
    simp only [f,ite_eq_left hs,ite_eq_left ht]
    rw [(CATZero.segment_spec C _ _).2.2 _ (parameter_mem hR hs) _ (parameter_mem hR ht),diam]
    have eq : parameter R s - parameter R t = (s-t)/(2*R) := by unfold parameter; ring
    rw [eq,abs_div,abs_of_pos (by positivity : 0<2*R),div_mul_cancel₀ _ (by positivity)]
  refine ⟨{ center := center, axis := f, starts := starts, intrinsic := intrinsic, bounded := ?_ },
    rfl, ?_, ?_⟩
  · intro i j s
    by_cases hs : |s|≤R
    · rw [←starts i j,intrinsic i j 0 s (by simpa using hR.le) hs,zero_sub,abs_neg]
    · simp only [f,ite_eq_right hs,dist_self,abs_nonneg]
  · intro i j
    have hm : |-R|≤R := by simp [abs_of_pos hR]
    simp only [f,ite_eq_left hm,parameter,neg_add_cancel,zero_div,(CATZero.segment_spec C _ _).1]
  · intro i j
    have hm : |R|≤R := by simp [abs_of_pos hR]
    have eq : parameter R R=1 := by unfold parameter; field_simp; ring
    simp only [f,ite_eq_left hm,eq,(CATZero.segment_spec C _ _).2.1]

namespace ColumnSegments

/-- The sign of the parameter selects a physical endpoint. -/
def endTime (R s : ℝ) : ℝ := if (0 : ℝ) ≤ s then R else -R

theorem abs_endTime (hR : 0≤R) (s : ℝ) : |endTime R s|=R := by
  unfold endTime
  split <;> simp [abs_of_nonneg hR]

theorem radial (C : CATZero X) (A : ColumnSegments I X k R) (hR : 0<R)
    (i : I) (j : Fin k) (s : ℝ) (hs : |s|≤R) :
    A.axis i j s = CATZero.segment C (A.center i) (A.axis i j (endTime R s)) (|s|/R) := by
  have h0 : |(0:ℝ)|≤R := by simpa using hR.le
  have he := abs_endTime hR.le s
  have d : dist (A.center i) (A.axis i j (endTime R s))=R := by
    rw [←A.starts i j,A.intrinsic _ _ _ _ h0 he.le,zero_sub,abs_neg,he]
  apply CATZero.eq_segment_of_dist C ⟨div_nonneg (abs_nonneg _) hR.le,(div_le_one hR).mpr hs⟩
  · rw [d,←A.starts i j,A.intrinsic _ _ _ _ h0 hs,zero_sub,abs_neg,div_mul_cancel₀ _ hR.ne']
  · rw [d,A.intrinsic _ _ _ _ hs he.le,sub_mul,one_mul,div_mul_cancel₀ _ hR.ne']
    unfold endTime
    split
    · rename_i h
      rw [abs_of_nonpos (by linarith [(abs_le.mp hs).2]),abs_of_nonneg h]
      ring
    · rename_i h
      rw [abs_of_nonneg (by linarith [(abs_le.mp hs).1]),abs_of_nonpos (by linarith)]
      ring

/-- Distance is convex along synchronized segments, allowing both endpoints to move. -/
theorem segment_dist_le (C : CATZero X) (x y x' y' : X) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    dist (CATZero.segment C x y u) (CATZero.segment C x' y' u)
    ≤ (1-u)*dist x x'+u*dist y y' := by
  have first := CATZero.radial_contraction C x y y' hu
  have other := CATZero.radial_contraction C y' x x' (t:=1-u) ⟨by linarith [hu.2],by linarith [hu.1]⟩
  rw [CATZero.segment_reverse C x y' hu,CATZero.segment_reverse C x' y' hu] at other
  exact (dist_triangle _ (CATZero.segment C x y' u) _).trans (by linarith)

theorem parallel_le (C : CATZero X) (A : ColumnSegments I X k R) (hR : 0<R)
    (i i' : I) (j : Fin k) (s K : ℝ) (hs : |s|≤R) (hcenter : dist (A.center i) (A.center i')≤K)
    (hend : dist (A.axis i j (endTime R s)) (A.axis i' j (endTime R s))≤K) :
    dist (A.axis i j s) (A.axis i' j s)≤K := by
  rw [A.radial C hR i j s hs,A.radial C hR i' j s hs]
  let u := |s|/R
  have hu : u ∈ Set.Icc (0:ℝ) 1 := ⟨div_nonneg (abs_nonneg _) hR.le,(div_le_one hR).mpr hs⟩
  apply (segment_dist_le C _ _ _ _ hu).trans
  nlinarith only [mul_le_mul_of_nonneg_left hcenter (sub_nonneg.mpr hu.2),
    mul_le_mul_of_nonneg_left hend hu.1]

theorem cross_le (C : CATZero X) (A : ColumnSegments I X k R) (hR : 0<R)
    (i : I) (j l : Fin k) (s t : ℝ) (hs : |s|≤R) (same : |s|=|t|)
    (cap : dist (A.axis i j (endTime R s)) (A.axis i l (endTime R t)) ≤ Real.sqrt 2*R+1) :
    dist (A.axis i j s) (A.axis i l t)≤Real.sqrt 2*|s|+|s|/R := by
  rw [A.radial C hR i j s hs,A.radial C hR i l t (same ▸ hs),←same]
  apply (CATZero.radial_contraction C _ _ _ ⟨div_nonneg (abs_nonneg _) hR.le,(div_le_one hR).mpr hs⟩).trans
  calc
    _ ≤ (|s|/R)*(Real.sqrt 2*R+1) := mul_le_mul_of_nonneg_left cap (div_nonneg (abs_nonneg _) hR.le)
    _ = _ := by field_simp

end ColumnSegments
end
end Hierarchy.AdaptiveProbe

end OAI
