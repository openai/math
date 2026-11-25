import Mathlib.LinearAlgebra.Transvection.Basic

/-! # A rank-one perturbation cutting off a Krylov chain -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Prescribe a linear functional on an independent family, then extend it from its span. -/
private theorem exists_functional_on_independent {W ι : Type*} [AddCommGroup W] [Module K W]
    {v : ι → W} (hv : LinearIndependent K v) (values : ι → K) :
    ∃ h : W →ₗ[K] K, ∀ i, h (v i) = values i := by
  let B := Basis.span hv
  obtain ⟨h, eq⟩ := (B.constr K values).exists_extend
  refine ⟨h, fun i ↦ ?_⟩
  have hbi := (LinearMap.congr_fun eq (B i)).trans (B.constr_basis K values i)
  simpa [B] using hbi

/-- Cut an independent Krylov chain after `b` terms by a rank-one change which fixes an
invariant subspace and preserves injectivity of `1 - C`. -/
theorem exists_krylov_cut (C : Module.End K V) (U : Submodule K V)
    (hU : ∀ u ∈ U, C u ∈ U) (hC : Function.Injective (1 - C : Module.End K V))
    (b : ℕ) (hb : 0 < b) (x : V)
    (hx : LinearIndependent K (fun i : Fin (b + 1) ↦ U.mkQ ((C ^ (i : ℕ)) x))) :
    ∃ C' : Module.End K V,
      (∀ u ∈ U, C' u = C u) ∧
      (∀ i : ℕ, i + 1 < b → C' ((C ^ i) x) = (C ^ (i + 1)) x) ∧
      C' ((C ^ (b - 1)) x) = 0 ∧
      Module.finrank K (LinearMap.range (C - C')) ≤ 1 ∧
      Function.Injective (1 - C' : Module.End K V) := by
  classical
  obtain ⟨ℓ, hℓ⟩ := exists_functional_on_independent hx
    (fun i ↦ if (i : ℕ) < b then (1 : K) else 0)
  let h := ℓ.comp U.mkQ
  let y := (C ^ b) x
  have hpow (i : ℕ) (hi : i ≤ b) :
      h ((C ^ i) x) = if i < b then 1 else 0 := hℓ ⟨i, by omega⟩
  have hy : h y = 0 := by simp [y, hpow]
  have next (i : ℕ) : C ((C ^ i) x) = (C ^ (i + 1)) x := by rw [pow_succ', End.mul_apply]
  let f := h.comp (1 - C : Module.End K V)
  let C' := C - f.smulRight y
  have cut (v : V) : C' v = C v - (h v - h (C v)) • y := by simp [C', f]
  refine ⟨C', ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have hz (v : V) (hv : v ∈ U) : h v = 0 := by
      simp [h, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr hv]
    simp [cut, hz u hu, hz (C u) (hU u hu)]
  · intro i hi
    rw [cut, next, hpow i (by omega), hpow (i + 1) (by omega)]
    simp [hi, show i < b by omega]
  · rw [cut, next, show b - 1 + 1 = b by omega, hpow (b - 1) (by omega), hpow b le_rfl]
    simp [y, show b - 1 < b by omega]
  · have hr : LinearMap.range (C - C') ≤ Submodule.span K {y} := by
      rintro _ ⟨v, rfl⟩
      simp only [C', sub_sub_cancel, LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    exact (Submodule.finrank_mono hr).trans (by simpa using (finrank_span_le_card (R := K) {y}))
  · have heq (v : V) : (1 - C' : Module.End K V) v =
        LinearEquiv.transvection hy ((1 - C : Module.End K V) v) := by
      simp only [LinearMap.sub_apply, End.one_apply, cut, LinearEquiv.transvection.apply, map_sub, sub_smul]
      abel
    exact fun v w hvw ↦ hC ((LinearEquiv.transvection hy).injective
      ((heq v).symm.trans (hvw.trans (heq w))))

end FiniteFourier
end LinearAlgebra
end OAI
