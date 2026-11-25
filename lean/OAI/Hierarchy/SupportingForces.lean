import OAI.Hierarchy.FlatPrices
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

namespace OAI
/-! # Simultaneous supporting forces on an arbitrary homogeneous spectral flat -/

namespace Hierarchy

open scoped BigOperators InnerProductSpace
open LinearAlgebra.SpectralBooks

namespace ForceApproximation

/-- A sublinear real-valued function has a supporting linear form at each point. -/
theorem exists_support {V : Type*} [AddCommGroup V] [Module ℝ V] (N : V → ℝ)
    (hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (add : ∀ x y, N (x+y) ≤ N x + N y) (x : V) :
    ∃ G : V →ₗ[ℝ] ℝ, G x = N x ∧ ∀ y, G y ≤ N y := by
  have hz : N 0 = 0 := by
    have h := hom 2 (by norm_num) 0
    rw [smul_zero] at h
    linarith
  have neg : -N x ≤ N (-x) := by have h := add x (-x); simp [hz] at h; linarith
  let compatible : ∀ c : ℝ, c • x = 0 → (RingHom.id ℝ c) • N x = 0 := by
    intro c hc
    rcases smul_eq_zero.mp hc with h | h
    · simp [h]
    · simp [h,hz]
  let l : V →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' x (N x) compatible
  have dom : ∀ y : l.domain, l y ≤ N y := by
    rintro ⟨y,hy⟩
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [LinearPMap.mkSpanSingleton'_apply]
    change c * N x ≤ N (c • x)
    rcases lt_trichotomy 0 c with hc|hc|hc
    · rw [hom _ hc]
    · simp [← hc,hz]
    · have h := mul_le_mul_of_nonneg_left neg (by linarith : 0 ≤ -c)
      have h' := hom (-c) (by linarith) (-x)
      rw [neg_smul,smul_neg,neg_neg] at h'
      nlinarith
  obtain ⟨G,eq,below⟩ := exists_extension_of_le_sublinear l N hom add dom
  refine ⟨G,?_,below⟩
  exact (eq ⟨x,Submodule.mem_span_singleton_self _⟩).trans
    (LinearPMap.mkSpanSingleton'_apply_self x (N x) compatible _)

end ForceApproximation

namespace HomogeneousFlat

variable {F : Type*} [Field F] {d : ℕ} (P : HomogeneousFlat F d)
variable {I : Type} [Fintype I]

/-- Forces on all terminal legs for the same price and the same supporting point. -/
theorem supporting_forces (T : SiteTensor.Raw.{0} I F) (x : I → (EuclideanSpace ℝ (Fin d))) :
    ∃ g : I → (EuclideanSpace ℝ (Fin d)), (∑ i, ⟪g i,x i⟫_ℝ) = P.prices.price T x ∧
      (∀ y, (∑ i, ⟪g i,y i⟫_ℝ) ≤ P.prices.price T y) ∧ ∑ i, g i = 0 := by
  classical
  let N := P.prices.price T
  have subadd (u v : I → (EuclideanSpace ℝ (Fin d))) : N (u+v) ≤ N u + N v := by
    have hm := (P.convex T).2 (Set.mem_univ u) (Set.mem_univ v)
      (show 0 ≤ (1/2:ℝ) by norm_num) (show 0 ≤ (1/2:ℝ) by norm_num) (by norm_num)
    rw [← smul_add,P.dilate T _ (1/2) (by norm_num)] at hm
    change 1/2 * N (u+v) ≤ 1/2 * N u + 1/2 * N v at hm
    linarith
  obtain ⟨L,exactAt,below⟩ := ForceApproximation.exists_support N (fun r hr z => P.dilate T z r hr) subadd x
  let ℓ (i : I) : (EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ := (L.comp (LinearMap.single ℝ (fun _ : I => (EuclideanSpace ℝ (Fin d))) i)).toContinuousLinearMap
  let g (i : I) := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (ℓ i)
  have rep (y : I → (EuclideanSpace ℝ (Fin d))) : (∑ i, ⟪g i, y i⟫_ℝ) = L y := by
    calc
      _ = ∑ i, L (Pi.single i (y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact InnerProductSpace.toDual_symm_apply
      _ = _ := by rw [← map_sum,LinearMap.sum_single_apply]
  refine ⟨g,(rep x).trans exactAt,fun y => (rep y).le.trans (below y),?_⟩
  have test := (rep (fun _ => ∑ i, g i)).le.trans (below _)
  rw [show N (fun _ => ∑ i, g i)=0 from P.prices.collapsed T _,← sum_inner] at test
  have sq := real_inner_self_nonneg (x := ∑ i, g i)
  exact inner_self_eq_zero.mp (le_antisymm test sq)

end HomogeneousFlat

end Hierarchy

end OAI
