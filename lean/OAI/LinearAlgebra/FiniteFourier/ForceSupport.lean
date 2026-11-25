import OAI.LinearAlgebra.FiniteFourier.Force
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Attainment and linear representation of spectral forces -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped InnerProductSpace BigOperators
open Submodule

/-- Joint convexity and positive homogeneity of a tensor price in its placements,
written in the equivalent sublinear form used to construct its forces. -/
structure SublinearPrice {V : Type*} [AddCommGroup V] [Module ℝ V] (h : V → ℝ) : Prop where
  hom : ∀ t : ℝ, 0 ≤ t → ∀ x, h (t • x) = t * h x
  add_le : ∀ x y, h (x + y) ≤ h x + h y

theorem SublinearPrice.zero {V : Type*} [AddCommGroup V] [Module ℝ V] {h : V → ℝ}
    (hs : SublinearPrice h) : h 0 = 0 := by simpa using hs.hom 0 (by norm_num) 0

/-- Hahn–Banach provides a supporting linear functional at any nonzero placement. -/
theorem SublinearPrice.exists_support {V : Type*} [AddCommGroup V] [Module ℝ V] {h : V → ℝ}
    (hs : SublinearPrice h) {u : V} (hu : u ≠ 0) :
    ∃ L : V →ₗ[ℝ] ℝ, L u = h u ∧ ∀ v, L v ≤ h v := by
  let L : V →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton u (h u) hu
  have hbound (v : L.domain) : L v ≤ h v := by
    obtain ⟨t, ht⟩ := mem_span_singleton.mp (show (v : V) ∈ ℝ ∙ u from v.2)
    obtain ⟨v, hv⟩ := v
    dsimp at ht
    subst v
    rw [show L ⟨t • u, hv⟩ = t * h u from LinearPMap.mkSpanSingleton'_apply ..]
    change t * h u ≤ h (t • u)
    rcases le_or_gt 0 t with ht | ht
    · rw [hs.hom _ ht]
    · have hop := hs.add_le u (-u)
      rw [add_neg_cancel, hs.zero] at hop
      rw [show t • u = (-t) • (-u) by simp, hs.hom _ (by linarith)]
      nlinarith [mul_nonneg (neg_nonneg.mpr ht.le) hop]
  obtain ⟨f, hext, hf⟩ := exists_extension_of_le_sublinear L h
    (fun t ht ↦ hs.hom t ht.le) hs.add_le hbound
  refine ⟨f, ?_, hf⟩
  exact (hext ⟨u, mem_span_singleton_self u⟩).trans (LinearPMap.mkSpanSingleton_apply ℝ ℝ hu (h u))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Each linear functional on the finite product of position spaces is a tuple
of Euclidean forces. -/
theorem exists_inner_tuple {ι : Type*} [Fintype ι] (L : (ι → E) →ₗ[ℝ] ℝ) :
    ∃ g : ι → E, ∀ x, L x = ∑ i, ⟪g i, x i⟫_ℝ := by
  classical
  let f (i : ι) : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    (L.comp (LinearMap.single ℝ (fun _ : ι ↦ E) i))
  let g i := (InnerProductSpace.toDual ℝ E).symm (f i)
  refine ⟨g, fun x ↦ ?_⟩
  have heq i (v : E) : ⟪g i, v⟫_ℝ = L (Pi.single i v) := by
    change (InnerProductSpace.toDual ℝ E (g i)) v = _
    rw [show InnerProductSpace.toDual ℝ E (g i) = f i from
      (InnerProductSpace.toDual ℝ E).apply_symm_apply _]
    rfl
  simp only [heq, ← map_sum, Finset.univ_sum_single]

/-- The bound on the price of a one-leg move bounds the norm of each force
at an attaining placement. -/
theorem exists_attaining_normalized_force {h : (Fin 4 → E) → ℝ}
    (hs : SublinearPrice h) {m : ℝ} (hm : 0 < m)
    (hleg : ∀ (i : Fin 4) (v : E), h (Pi.single i v) ≤ m * ‖v‖)
    {u : Fin 4 → E} (hu : u ≠ 0) :
    ∃ g : Fin 4 → E, (∀ i, ‖g i‖ ≤ 1) ∧
      m * (∑ i, ⟪g i, u i⟫_ℝ) = h u ∧ IsNormalizedForce m h g := by
  obtain ⟨L, hL, hsup⟩ := hs.exists_support hu
  obtain ⟨a, ha⟩ := exists_inner_tuple L
  let g i := m⁻¹ • a i
  have hg x : m * (∑ i, ⟪g i, x i⟫_ℝ) = L x := by
    rw [ha]
    simp [g, real_inner_smul_left, ← Finset.mul_sum, hm.ne']
  refine ⟨g, fun i ↦ ?_, (hg _).trans hL, fun x ↦ (hg x).le.trans (hsup x)⟩
  have h := (hg (Pi.single i (g i))).le.trans ((hsup _).trans (hleg _ _))
  have heq : (∑ j, ⟪g j, (Pi.single i (g i) : Fin 4 → E) j⟫_ℝ) = ‖g i‖ ^ 2 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  rw [heq] at h
  have hh := (mul_le_mul_iff_right₀ hm).mp h
  nlinarith [norm_nonneg (g i)]

end FiniteFourier
end LinearAlgebra
end OAI
