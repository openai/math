import OAI.Hierarchy.ProbeOuterMesh

namespace OAI
/-! # Uniform mesh size and total nominal outer control allowance -/

namespace Hierarchy.AdaptiveProbe

open scoped BigOperators
noncomputable section

/-- The mesh is chosen before the width or the number of payloads. Bounds on
squared payload multiplicities and on gradient squares are per payload. -/
theorem choose_outer_mesh {a s₀ : ℝ} (ha : 0<a) (hs : 0<s₀) (V G : ℝ) :
    ∃ m : ℕ, 0<m ∧ V≤a*m ∧ G≤s₀*a*m := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max 0 (max (V/a) (G/(s₀*a))))
  have n : (0:ℝ)<m := (le_max_left ..).trans_lt hm
  have vp := (le_max_left (V/a) (G/(s₀*a))).trans ((le_max_right ..).trans hm.le)
  have gp := (le_max_right (V/a) (G/(s₀*a))).trans ((le_max_right ..).trans hm.le)
  exact ⟨m,by exact_mod_cast n,by simpa [mul_comm] using (div_le_iff₀ ha).mp vp,
    by simpa [mul_comm] using (div_le_iff₀ (mul_pos hs ha)).mp gp⟩

/-- On each step the curvature contribution costs at most one half of its
normalized step length. -/
theorem mesh_quadratic {δ V C a s n : ℝ} (positive : 0<s*a) (dn : 0≤δ) (nn : 0≤n)
    (uniform : V≤C*n) (mesh : δ*C≤2*(s*a)) :
    δ^2*V/(4*s*a) ≤ δ*n/2 := by
  have scaled := mul_le_mul_of_nonneg_left uniform (sq_nonneg δ)
  have small := mul_le_mul_of_nonneg_right mesh (mul_nonneg dn nn)
  apply (div_le_iff₀ (by nlinarith : 0<4*s*a)).mpr
  nlinarith only [scaled,small]

theorem injected_curvature {w m j : ℕ} {C a : ℝ} (hm : 0<m) (hw : m≤w)
    (hC : 0≤C) (ha : 0<a) (large : C≤a*m) :
    payloadSlice m w j*C≤2*a := by
  obtain ⟨_,b⟩ := payloadSlice_bounds hm hw j
  have sm : (0:ℝ)<m := by exact_mod_cast hm
  calc
    _ ≤ (2/(m:ℝ))*(a*m) := mul_le_mul b large hC (by positivity)
    _ = _ := by field_simp

theorem cooled_curvature {m j : ℕ} {C a s₀ : ℝ} (hm : 0<m) (hs : 0<s₀)
    (_endLe : s₀≤1) (hC : 0≤C) (ha : 0<a) (large : C≤s₀*a*m) :
    (clockTime s₀ m j-clockTime s₀ m (j+1))*C ≤ 2*(s₀*a) := by
  rw [clock_drop]
  have sm : (0:ℝ)<m := by exact_mod_cast hm
  have bound : (1-s₀)/(m:ℝ)≤1/(m:ℝ) := div_le_div_of_nonneg_right (by linarith) sm.le
  calc
    _ ≤ (1/(m:ℝ))*(s₀*a*m) := mul_le_mul bound large hC (by positivity)
    _ = s₀*a := by field_simp
    _ ≤ _ := by linarith [mul_pos hs ha]

/-- The time decrease uses the left-endpoint values of the actual protocol
barrier. Its integral bound remains valid for the real finite mesh. -/
theorem outer_cooling_sum {m : ℕ} {r scale s₀ : ℝ} (hm : 0<m) (hs : 0<s₀) (h₁ : s₀≤1)
    (hr : 0<r) (hr₁ : r≤1) (nn : 0≤scale) (integral : scale*(1-Real.log r)≤1) :
    ∑ j ∈ Finset.range m, ((1-s₀)/(m:ℝ))*
      (scale*min (1/clockTime s₀ m j) (1/r)+1) ≤ 2 := by
  let t := clockTime s₀ m
  have ends := clock_endpoints (s₀:=s₀) hm
  have sm : (0:ℝ)<m := by exact_mod_cast hm
  have main := cooling_allowance hr hr₁ t m ends.1
    (fun j hj=> hs.trans_le (clock_bounds hs h₁ hm j hj).1)
    (fun j _=>by
      have h := clock_drop s₀ m j
      have n := div_nonneg (sub_nonneg.mpr h₁) sm.le
      dsimp [t]; linarith)
  change (∑ j ∈ Finset.range m, (t j-t (j+1))*min (1/t j) (1/r))≤_ at main
  have split (j : ℕ) : ((1-s₀)/(m:ℝ))*(scale*min (1/t j) (1/r)+1) =
      scale*((t j-t (j+1))*min (1/t j) (1/r)) + ((1-s₀)/(m:ℝ)) := by
    dsimp [t]; rw [clock_drop]; ring
  change ∑ j ∈ Finset.range m, _*(scale*min (1/t j) (1/r)+1)≤2
  simp_rw [split]
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  have total : (∑ _ ∈ Finset.range m, (1-s₀)/(m:ℝ)) = 1-s₀ := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    field_simp
  rw [total]
  linarith [mul_le_mul_of_nonneg_left main nn]

end
end Hierarchy.AdaptiveProbe

end OAI
