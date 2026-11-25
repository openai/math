import OAI.Geometry.HyperbolicGroups.CATZero
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI
/-! # The finite-segment estimate for the long altimeter wires -/

namespace Hierarchy.AdaptiveProbe

open HyperbolicObstruction
open scoped InnerProductSpace
noncomputable section

/-- A reading at the far end and a reading on the same segment at radius
`r` differ by at most the squared center distance divided by `2r`. -/
theorem segment_readout {X : Type*} [MetricSpace X] (C : CATZero X)
    (a b q : X) {M r : ℝ} (length : dist a b = M) (hr : 0 < r) (hrM : r ≤ M) :
    let p := CATZero.segment C a b (r/M)
    0 ≤ (dist q p-r) - (dist q b-M) ∧
      (dist q p-r) - (dist q b-M) ≤ (dist q a)^2/(2*r) := by
  let t := r/M
  have hM := hr.trans_le hrM
  have ht : t ∈ Set.Icc (0:ℝ) 1 := ⟨div_nonneg hr.le hM.le, (div_le_one hM).mpr hrM⟩
  have tM : t*M=r := div_mul_cancel₀ r hM.ne'
  let p := CATZero.segment C a b t
  let D := dist q a
  let E := dist q b - M
  let e := dist q p - r
  have endpoint : dist q b = M+E := by dsimp [E]; ring
  have middle : dist q p = r+e := by dsimp [e]; ring
  have right : dist p b = M-r := by
    dsimp only [p]
    rw [CATZero.segment_right C a b ht, length]
    linarith
  have low : E ≤ e := by
    have h := dist_triangle q p b
    rw [endpoint,middle,right] at h
    linarith
  have E₁ : E ≤ D := by have h := dist_triangle q a b; rw [length,endpoint] at h; dsimp [D]; linarith
  have E₂ : -D ≤ E := by
    have h := dist_triangle a q b
    rw [length,dist_comm a q,endpoint] at h
    dsimp [D]; linarith
  have hsq : E^2 ≤ D^2 := sq_le_sq' E₂ E₁
  have cn := CATZero.segment_cn C a b q ht
  change dist q p ^ 2 ≤ (1-t)*D^2 + t*(dist q b)^2 - t*(1-t)*(dist a b)^2 at cn
  rw [middle, endpoint, length] at cn
  have expansion :
      (1-t)*D^2 + t*(M+E)^2 - t*(1-t)*M^2 =
        r^2 + 2*r*E + D^2 + t*(E^2-D^2) := by rw [←tM]; ring
  rw [expansion] at cn
  change 0 ≤ e-E ∧ e-E ≤ D^2/(2*r)
  refine ⟨sub_nonneg.mpr low, (le_div_iff₀ (by positivity)).mpr ?_⟩
  nlinarith only [cn, sq_nonneg e, mul_nonpos_of_nonneg_of_nonpos ht.1 (sub_nonpos.mpr hsq)]

/-- In a Euclidean realization the physical reading tends to its signed
coordinate, with the same uniform error for every unit direction. -/
theorem euclidean_readout {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u α : E) (hα : ‖α‖=1) {r : ℝ} (hr : ‖u‖ < r) :
    0 ≤ (‖u + r • α‖-r) - ⟪u,α⟫_ℝ ∧
      (‖u + r • α‖-r) - ⟪u,α⟫_ℝ ≤ ‖u‖^2/(2*(r-‖u‖)) := by
  let z := ‖u + r • α‖
  let c := ⟪u,α⟫_ℝ
  have hb : |c| ≤ ‖u‖ := by simpa [c,hα] using abs_real_inner_le_norm u α
  have hz : 0 ≤ z := norm_nonneg _
  have hc := abs_le.mp hb
  have hpos : 0 < r+c := by linarith
  have hsq : z^2 = ‖u‖^2+2*r*c+r^2 := by
    simp only [z,c,norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hα,
      mul_one, abs_of_pos ((norm_nonneg u).trans_lt hr)]
    ring
  have proj : r+c ≤ z := by
    apply le_of_not_gt
    intro h
    have strict := mul_pos (sub_pos.mpr h) (add_pos_of_pos_of_nonneg hpos hz)
    have bound := sq_le_sq' hc.1 hc.2
    nlinarith only [hsq, strict, bound]
  have factor : (z-(r+c))*(z+(r+c)) = ‖u‖^2-c^2 := by nlinarith only [hsq]
  change 0 ≤ z-r-c ∧ z-r-c ≤ _
  refine ⟨by linarith, (le_div_iff₀ (by linarith)).mpr ?_⟩
  have denom : 2*(r-‖u‖) ≤ z+(r+c) := by linarith
  have bound := mul_le_mul_of_nonneg_left denom (sub_nonneg.mpr proj)
  nlinarith only [factor, bound, sq_nonneg c]

end
end Hierarchy.AdaptiveProbe

end OAI
