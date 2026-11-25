import OAI.LinearAlgebra.SpectralBooks.SectorTriangle
import OAI.LinearAlgebra.SpectralBooks.SectorQuadratic
import OAI.LinearAlgebra.SpectralBooks.NormPatch

/-! # The metric of a bounded Euclidean sector, including degenerate sectors -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction Set

/-- All squared distances on the closed parameter triangle agree with the Euclidean
quadratic form determined by the two radial speeds and the equal-radius separation.
This includes the semidefinite case in which some parameter points coincide. -/
theorem sectorMap_triangle_dist_sq {X : Type*} [MetricSpace X]
    (g : IsGeodesic X) (hB : SectorBusemann X) (hX : ScaledSectorNormRigidity X)
    {a b : ℝ → X} {A B c R : ℝ} (hR : 0 < R)
    (ha : ∀ r ∈ Icc 0 R, ∀ s ∈ Icc 0 R, dist (a r) (a s) = |r-s| * A)
    (hb : ∀ r ∈ Icc 0 R, ∀ s ∈ Icc 0 R, dist (b r) (b s) = |r-s| * B)
    (hsep : ∀ r ∈ Icc 0 R, dist (a r) (b r) = c*r)
    {p q : ℝ × ℝ} (hp : p ∈ sectorDomain (Icc 0 R)) (hq : q ∈ sectorDomain (Icc 0 R)) :
    dist (sectorMap g a b p) (sectorMap g a b q) ^ 2 =
      (p.1-q.1)^2*A^2 + (p.2-q.2)^2*B^2 + (p.1-q.1)*(p.2-q.2)*(A^2+B^2-c^2) := by
  classical
  let H := sectorMap g a b
  let C := sectorDomain (Icc 0 R)
  obtain ⟨N, hN⟩ := sectorMap_triangle_seminorm g hB hR ha hb hsep
  change ∀ p ∈ C, ∀ q ∈ C, dist (H p) (H q) = N (p-q) at hN
  have hfit {I : Type} [Fintype I] (u : I → ℝ × ℝ) :
      ∃ k : ℝ × ℝ, ∃ s : ℝ, 0 < s ∧ ∀ i, k+s • u i ∈ C := by
    obtain ⟨k,s,hs,hk⟩ := exists_scaled_configuration_in_open
      (sectorDomain_Icc_interior_nonempty hR) isOpen_interior (Finset.univ.image u)
    exact ⟨k,s,hs,fun i ↦ interior_subset (hk _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))⟩
  let e : ℝ × ℝ := (1,0)
  let f : ℝ × ℝ := (0,1)
  have he : R • e = (R,0) := by simp [e]
  have hf : R • f = (0,R) := by simp [f]
  have hRe : R • e ∈ C := by
    rw [he]
    exact ⟨hR.le, le_rfl, by simpa using hR.le, by simp⟩
  have hRf : R • f ∈ C := by
    rw [hf]
    exact ⟨le_rfl, hR.le, by simpa using hR.le, by simp⟩
  have h0 : (0 : ℝ × ℝ) ∈ C := ⟨le_rfl, le_rfl, by norm_num, by simpa using hR.le⟩
  have hR' : R ∈ Icc 0 R := ⟨hR.le, le_rfl⟩
  have h0' : (0 : ℝ) ∈ Icc 0 R := ⟨le_rfl, hR.le⟩
  have haxes (r : ℝ) (hr : r ∈ Icc 0 R) : H (r,0) = a r ∧ H (0,r) = b r :=
    sectorMap_axes g hsep hr.1 hr
  have ha0 : H 0 = a 0 := (haxes 0 h0').1
  have hb0 : H 0 = b 0 := (haxes 0 h0').2
  have hA := hN _ hRe _ h0
  rw [sub_zero, map_smul_eq_mul, Real.norm_of_nonneg hR.le, he, (haxes R hR').1,
    ha0, ha R hR' 0 h0', sub_zero, abs_of_pos hR] at hA
  have hB' := hN _ hRf _ h0
  rw [sub_zero, map_smul_eq_mul, Real.norm_of_nonneg hR.le, hf, (haxes R hR').2,
    hb0, hb R hR' 0 h0', sub_zero, abs_of_pos hR] at hB'
  have hc := hN _ hRe _ hRf
  rw [←smul_sub, map_smul_eq_mul, Real.norm_of_nonneg hR.le, he, hf, (haxes R hR').1,
    (haxes R hR').2, hsep R hR', mul_comm c R] at hc
  have heN := (mul_left_cancel₀ hR.ne' hA).symm
  have hfN := (mul_left_cancel₀ hR.ne' hB').symm
  have hdN := (mul_left_cancel₀ hR.ne' hc).symm
  have hid : (p.1-q.1) • e - (q.2-p.2) • f = p-q := by ext <;> simp [e, f]
  have hpoly := patch_seminorm_sq_of_rigidity hX hfit H N hN e f (p.1-q.1) (q.2-p.2)
  rw [hid, heN, hfN, hdN, ←hN _ hp _ hq] at hpoly
  change dist (H p) (H q) ^ 2 = _
  rw [hpoly]
  ring

end SpectralBooks
end LinearAlgebra
end OAI
