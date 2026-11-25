import OAI.Computability.BorderVNP.CoverLorentzPlane

/-!
# Geodesic sides of the compact Dirichlet tile

On a bounded neighborhood of the closed tile, only finitely many translates of
the base site can contribute a bisector. The hyperbolic bisectors in upper
half-plane coordinates are vertical lines or circles with center on the real axis.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Set UpperHalfPlane

/-- The boundary of the tile lies on finitely many bisectors to distinct translated sites. -/
theorem dirichlet_frontier_bisectors (l : ℕ) :
    ∃ s : Finset (gamma (l+1)), (∀ u ∈ s, u ≠ 1) ∧
      ∀ z ∈ frontier (dirichlet (l+1)), ∃ u ∈ s, dist z I = dist z (gammaSL (l+1) u • I) := by
  classical
  obtain ⟨r,_,hr⟩ := dirichlet_bounded (l+1)
  let b := r + 1
  let K := Metric.closedBall I (2*b)
  have hf := finite_sites (l+1) (ProperSpace.isCompact_closedBall I (2*b))
  let s := hf.toFinset.erase 1
  have hs (u : gamma (l+1)) : u ∈ s ↔ u ≠ 1 ∧ dist (gammaSL (l+1) u • I) I ≤ 2*b := by
    rw [Finset.mem_erase,hf.mem_toFinset]; rfl
  refine ⟨s,fun u hu => (hs u).mp hu |>.1,?_⟩
  intro z hz
  have hzD : z ∈ dirichlet (l+1) := by
    have h := frontier_subset_closure hz
    rwa [(dirichlet_compact _).isClosed.closure_eq] at h
  by_contra! no
  let U : Set ℍ := Metric.ball I b ∩ ⋂ u ∈ s, {v : ℍ | dist v I < dist v (gammaSL (l+1) u • I)}
  have hopen : IsOpen U := Metric.isOpen_ball.inter (s.finite_toSet.isOpen_biInter
    (fun _ _ => isOpen_lt (by fun_prop) (by fun_prop)))
  have hmem : z ∈ U := by
    refine ⟨(hr hzD).trans_lt (lt_add_one r),?_⟩
    exact mem_iInter₂.mpr fun u hu => lt_of_le_of_ne (hzD u) (no u hu)
  have hsub : U ⊆ dirichlet (l+1) := by
    intro v hv u
    by_cases hu : u ∈ s
    · exact (mem_iInter₂.mp hv.2 u hu).le
    by_cases he : u = 1
    · simp [he]
    have hd : 2*b < dist (gammaSL (l+1) u • I) I :=
      lt_of_not_ge (fun h => hu ((hs _).2 ⟨he,h⟩))
    have ht := dist_triangle I v (gammaSL (l+1) u • I)
    have hball : dist v I < b := hv.1
    rw [dist_comm I v,dist_comm I (gammaSL (l+1) u • I)] at ht
    linarith
  exact hz.2 (interior_maximal hsub hopen hmem)

private theorem bisector_equation {w z : ℍ} (h : dist z I = dist z w) :
    w.im*(z.re^2+z.im^2+1) = (z.re-w.re)^2 + z.im^2 + w.im^2 := by
  have e := congrArg Real.cosh h
  rw [cosh_dist',cosh_dist',I_re,I_im,sub_zero,one_pow,mul_one] at e
  field_simp [z.im_ne_zero,w.im_ne_zero] at e
  linarith only [e]

/-- Distinct-site bisectors are geodesic lines in the upper half-plane model. -/
theorem bisector_line_or_circle {w : ℍ} (hw : w ≠ I) :
    (∃ a : ℝ, ∀ z : ℍ, dist z I = dist z w → z.re = a) ∨
    (∃ a R : ℝ, 0 < R ∧ ∀ z : ℍ, dist z I = dist z w →
      (z.re-a)^2 + z.im^2 = R^2) := by
  by_cases hy : w.im = 1
  · left
    have hx : w.re ≠ 0 := by
      intro h
      apply hw
      exact UpperHalfPlane.ext (Complex.ext (h.trans I_re.symm) (hy.trans I_im.symm))
    refine ⟨w.re/2,fun z h => ?_⟩
    have e := bisector_equation h
    rw [hy] at e
    have prod : w.re * (z.re - w.re/2) = 0 := by linarith only [e]
    exact sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left hx)
  · right
    let t := w.im - 1
    let k := w.re/t
    have ht : t ≠ 0 := sub_ne_zero.mpr hy
    have hp : 0 < w.im*(1+k^2) := mul_pos w.im_pos (by positivity)
    refine ⟨-k,Real.sqrt (w.im*(1+k^2)),Real.sqrt_pos.mpr hp,?_⟩
    intro z h
    rw [Real.sq_sqrt hp.le]
    have e := bisector_equation h
    dsimp [k]
    field_simp [ht]
    dsimp [t]
    linear_combination (w.im-1) * e

end Cover

end BorderVNP
end Computability
end OAI
