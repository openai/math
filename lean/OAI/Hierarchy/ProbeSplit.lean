import OAI.Hierarchy.ProbeAxisPlane
import OAI.Hierarchy.ProbeCalibration

namespace OAI
/-! # Removing one common signed axis from a family of marked columns -/

namespace Hierarchy.AdaptiveProbe
open HyperbolicObstruction
noncomputable section

universe u v

/-- Oriented limit axes of the columns. All coordinates of any one column
are perpendicular, and all columns use the same orientation of each axis. -/
structure Axes (I : Type v) (X : Type u) [MetricSpace X] (k : ℕ) where
  center : I → X
  axis : I → Fin k → ℝ → X
  starts : ∀ i j, axis i j 0=center i
  isometry : ∀ i j, Isometry (axis i j)
  orthogonal : ∀ i j l, j≠l → ∀ s t, dist (axis i j s) (axis i l t)^2=s^2+t^2
  parallel : ∀ i i' j, ∃ C : ℝ, ∀ t, dist (axis i j t) (axis i' j t) ≤ C

variable {I : Type v} {X : Type u} [MetricSpace X] {k : ℕ}

private theorem line_over_mark {b : X → ℝ} {r l : ℝ → X} {c : ℝ}
    (C : CATZero X) (hb : LipschitzWith 1 b) (iso : Isometry l)
    (cal : ∀ t, b (l t)=c+t) (near : ∃ K : ℝ, ∀ t, dist (l t) (r t) ≤ K) :
    ∃ y : CATZero.Transverse b r, ∀ t, CATZero.Transverse.line y (c+t)=l t := by
  have hn := CATZero.Calibrated.shift_to_zero iso (fun t => (cal t).trans (add_comm _ _)) near
  let y : CATZero.Transverse b r := ⟨l (0-c),_,hn,rfl⟩
  refine ⟨y, ?_⟩
  have eqn := CATZero.Transverse.line_eq C hb hn y rfl
  intro t
  rw [eqn]
  simp

theorem split_axis (C : CATZero X) (base : I) (A : Axes I X (k+1)) :
    ∃ (Y : Type u) (_ : MetricSpace Y), CATZero Y ∧
      ∃ (rest : Axes I Y k) (phase : I → ℝ) (e : ℝ → Y → X),
        (∀ s t v w, dist (e s v) (e t w)^2=(s-t)^2+dist v w^2) ∧
        (∀ i t, e (phase i+t) (rest.center i)=A.axis i 0 t) ∧
        ∀ i j t, e (phase i) (rest.axis i j t)=A.axis i j.succ t := by
  classical
  let r := A.axis base 0
  let b := calibration r
  have hb : LipschitzWith 1 b := calibration_lipschitz _ (A.isometry base 0)
  let c (i : I) := b (A.center i)
  let Y := CATZero.Transverse b r
  let e (t : ℝ) (p : Y) := CATZero.Transverse.line p t
  have metric (s t : ℝ) (v w : Y) : dist (e s v) (e t w)^2=(s-t)^2+dist v w^2 :=
    (CATZero.Transverse.dist_line_sq C hb v w s t).trans (add_comm _ _)
  have fiber (s : ℝ) (v w : Y) : dist (e s v) (e s w)=dist v w := by
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    simpa using metric s s v w
  have phase (i : I) (t : ℝ) : b (A.axis i 0 t)=c i+t := by
    simpa only [b,c,A.starts] using calibration_parallel C r (A.axis i 0) (A.isometry base 0)
      (A.isometry i 0) (A.parallel i base 0) t
  choose y hy using fun i => line_over_mark C hb (A.isometry i 0) (phase i) (A.parallel i base 0)
  have hc (i : I) : e (c i) (y i)=A.center i := by simpa only [add_zero,A.starts,e] using hy i 0
  have represented (i : I) (j : Fin k) (v : ℝ) : ∃ z : Y, e (c i) z=A.axis i j.succ v := by
    obtain ⟨l,iso,origin,cal,near⟩ := parallel_through_orthogonal_axis C (A.axis i 0) (A.axis i j.succ)
      (A.isometry i 0) (A.isometry i j.succ) ((A.starts ..).trans (A.starts ..).symm)
      (A.orthogonal i 0 j.succ (Fin.succ_ne_zero j).symm) b hb (c i) (phase i) v
    obtain ⟨K,hK⟩ := A.parallel i base 0
    have bound : ∀ t, dist (l t) (r t) ≤ |v|+K := fun t =>
      (dist_triangle _ (A.axis i 0 t) _).trans (add_le_add (near t) (hK t))
    obtain ⟨z,hz⟩ := line_over_mark C hb iso cal ⟨_,bound⟩
    exact ⟨z, (by simpa only [add_zero,e] using hz 0 : e (c i) z=l 0).trans origin⟩
  choose z hz using represented
  let rest : Axes I Y k := {
    center := y
    axis := z
    starts := by
      intro i j
      apply dist_eq_zero.mp
      rw [←fiber (c i),hz,hc,A.starts,dist_self]
    isometry := by
      intro i j
      exact Isometry.of_dist_eq fun s t => by rw [←fiber (c i),hz,hz,(A.isometry i j.succ).dist_eq]
    orthogonal := by
      intro i j l ne s t
      rw [←fiber (c i),hz,hz]
      exact A.orthogonal i j.succ l.succ (fun eqn => ne (Fin.succ_injective _ eqn)) s t
    parallel := by
      intro i i' j
      obtain ⟨K,hK⟩ := A.parallel i i' j.succ
      refine ⟨K,fun t => le_trans ?_ (hK t)⟩
      apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
      have h := metric (c i) (c i') (z i j t) (z i' j t)
      rw [hz,hz] at h
      linarith [sq_nonneg (c i-c i')]
  }
  exact ⟨Y,inferInstance,CATZero.Transverse.catZero C hb,rest,c,e,metric,hy,hz⟩

end
end Hierarchy.AdaptiveProbe

end OAI
