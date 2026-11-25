import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-! # Decomposition of a real continuous functional into positive functionals -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

private theorem norm_sup_zero_add_le (f g : C(X, ℝ)) :
    ‖(f + g) ⊔ 0‖ ≤ ‖f ⊔ 0‖ + ‖g ⊔ 0‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro x
  change |max (f x + g x) 0| ≤ _
  rw [abs_of_nonneg (le_max_right _ _)]
  apply max_le
  · have hf := (f ⊔ 0).apply_le_norm x
    have hg := (g ⊔ 0).apply_le_norm x
    change max (f x) 0 ≤ _ at hf
    change max (g x) 0 ≤ _ at hg
    exact add_le_add ((le_max_left _ _).trans hf) ((le_max_left _ _).trans hg)
  · positivity

private theorem norm_sup_zero_smul (c : ℝ) (hc : 0 ≤ c) (f : C(X, ℝ)) :
    ‖(c • f) ⊔ 0‖ = c * ‖f ⊔ 0‖ := by
  have h : (c • f) ⊔ 0 = c • (f ⊔ 0) := by
    ext x
    change max (c * f x) 0 = c * max (f x) 0
    rw [mul_max_of_nonneg _ _ hc, mul_zero]
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

private theorem norm_le_parts (f : C(X, ℝ)) : ‖f‖ ≤ ‖f ⊔ 0‖ + ‖(-f) ⊔ 0‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro x
  have hf := (f ⊔ 0).apply_le_norm x
  have hn := ((-f) ⊔ 0).apply_le_norm x
  change max (f x) 0 ≤ _ at hf
  change max (-f x) 0 ≤ _ at hn
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [le_max_left (-f x) 0, norm_nonneg (f ⊔ 0)]
  · linarith [le_max_left (f x) 0, norm_nonneg ((-f) ⊔ 0)]

/-- Every real continuous functional on continuous functions on a compact space
is the difference of two positive linear maps. -/
theorem exists_positiveLinearMap_sub (L : C(X, ℝ) →L[ℝ] ℝ) :
    ∃ P N : C(X, ℝ) →ₚ[ℝ] ℝ, ∀ f, L f = P f - N f := by
  let D : Submodule ℝ (C(X, ℝ) × C(X, ℝ)) :=
    { carrier := {p | p.1 = p.2}
      zero_mem' := rfl
      add_mem' := fun {a b} ha hb ↦ congrArg₂ (· + ·) ha hb
      smul_mem' := fun c _ ha ↦ congrArg (c • ·) ha }
  let F : (C(X, ℝ) × C(X, ℝ)) →ₗ.[ℝ] ℝ :=
    ⟨D, L.toLinearMap.comp ((LinearMap.fst ℝ _ _).comp D.subtype)⟩
  let B (p : C(X, ℝ) × C(X, ℝ)) := ‖L‖ * (‖p.1 ⊔ 0‖ + ‖(-p.2) ⊔ 0‖)
  obtain ⟨G, hdiag, hG⟩ := exists_extension_of_le_sublinear F B
    (by
      intro c hc p
      change ‖L‖ * (‖(c • p.1) ⊔ 0‖ + ‖(-(c • p.2)) ⊔ 0‖) = c * B p
      rw [← smul_neg, norm_sup_zero_smul c hc.le, norm_sup_zero_smul c hc.le]
      dsimp [B]
      ring)
    (by
      intro p q
      change ‖L‖ * (‖(p.1 + q.1) ⊔ 0‖ + ‖(-(p.2 + q.2)) ⊔ 0‖) ≤ B p + B q
      rw [neg_add]
      dsimp [B]
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ L.opNorm_nonneg
      linarith [norm_sup_zero_add_le p.1 q.1, norm_sup_zero_add_le (-p.2) (-q.2)])
    (by
      intro p
      have hp : p.val.1 = p.val.2 := p.property
      change L p.val.1 ≤ ‖L‖ * (‖p.val.1 ⊔ 0‖ + ‖(-p.val.2) ⊔ 0‖)
      rw [← hp]
      exact (le_abs_self _).trans <| (L.le_opNorm _).trans <|
        mul_le_mul_of_nonneg_left (norm_le_parts _) L.opNorm_nonneg)
  let P := G.comp (LinearMap.inl ℝ C(X, ℝ) C(X, ℝ))
  let N := -G.comp (LinearMap.inr ℝ C(X, ℝ) C(X, ℝ))
  have hP (f : C(X, ℝ)) (hf : 0 ≤ f) : 0 ≤ P f := by
    have h := hG (-f, 0)
    have hf' : -f ≤ 0 := fun x ↦ neg_nonpos.mpr (hf x)
    have hneg : (-f, (0 : C(X, ℝ))) = -(f, 0) := by simp
    have hbound : B (-f, 0) = 0 := by simp [B, sup_eq_right.mpr hf']
    rw [hbound, hneg, map_neg, neg_nonpos] at h
    exact h
  have hN (f : C(X, ℝ)) (hf : 0 ≤ f) : 0 ≤ N f := by
    have h := hG (0, f)
    have hf' : -f ≤ 0 := fun x ↦ neg_nonpos.mpr (hf x)
    simpa [B, sup_eq_right.mpr hf', N] using h
  refine ⟨{ P with monotone' := fun a b h ↦ ?_ }, { N with monotone' := fun a b h ↦ ?_ }, ?_⟩
  · simpa using hP (b - a) (fun x ↦ sub_nonneg.mpr (h x))
  · simpa using hN (b - a) (fun x ↦ sub_nonneg.mpr (h x))
  · intro f
    have h := (hdiag ⟨(f, f), rfl⟩).symm
    change L f = G (f, 0) - -G (0, f)
    change L f = G (f, f) at h
    rw [h, sub_neg_eq_add, ← map_add]
    simp

end SpectralBooks
end LinearAlgebra
end OAI
