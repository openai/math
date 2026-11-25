import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic

/-! # Paired coordinates at a prime Fourier endpoint

A routing vector of norm one specifies the distinguished axis in both halves
of the array. The remaining axes use a basis of its perpendicular subspace in
the first half and the paired dual basis in the second half.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Module
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- Split off a normalized vector using its coordinate functional. -/
private def normOneSplit (f : E →ₗ[K] K) (d : E) (hd : f d = 1) :
    E ≃ₗ[K] K × LinearMap.ker f where
  toFun x := (f x, ⟨x - f x • d, by simp [LinearMap.mem_ker, hd]⟩)
  invFun u := u.1 • d + (u.2 : E)
  left_inv x := by simp
  right_inv := by
    rintro ⟨c, x⟩
    have hx : f x = 0 := x.property
    apply Prod.ext
    · simp [hd, hx]
    · apply Subtype.ext
      simp [hd, hx]
  map_add' x y := by
    apply Prod.ext
    · exact map_add f _ _
    · apply Subtype.ext
      change x + y - f (x + y) • d = (x - f x • d) + (y - f y • d)
      rw [map_add, add_smul]
      abel
  map_smul' a x := by
    apply Prod.ext
    · exact map_smul f _ _
    · apply Subtype.ext
      change a • x - f (a • x) • d = a • (x - f x • d)
      rw [map_smul, smul_sub, smul_smul, smul_eq_mul]

variable [FiniteDimensional K E]

/-- Paired charts for the two ordinary halves of a routing label. The
distinguished coordinate is the same functional in both halves, while the
auxiliary axes contribute the usual coordinate dot product to the pairing. -/
theorem exists_primeEndpointLabelCharts (B : LinearMap.BilinForm K E)
    (hB : B.Nondegenerate) (hs : B.IsSymm) (d : E) (hd : B d d = 1) :
    ∃ p q : E ≃ₗ[K] K × (Fin (finrank K E - 1) → K),
      (∀ x, (p x).1 = B d x ∧ (q x).1 = B d x) ∧
      p d = (1, 0) ∧ q d = (1, 0) ∧
      ∀ x y, B x y = (p x).1 * (q y).1 + ∑ i, (p x).2 i * (q y).2 i := by
  classical
  let U := LinearMap.ker (B d)
  let e := normOneSplit (B d) d hd
  have dimU : finrank K U = finrank K E - 1 := by
    have h := e.finrank_eq
    change finrank K E = finrank K (K × U) at h
    rw [Module.finrank_prod, Module.finrank_self] at h
    omega
  have hU : (B.restrict U).Nondegenerate := by
    have h := B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl
      (show B d d ≠ 0 by rw [hd]; exact one_ne_zero)
    rw [LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker] at h
    exact h
  let b := (Module.finBasis K U).reindex (finCongr dimU)
  let b' := (B.restrict U).dualBasis hU b
  let p := e.trans ((LinearEquiv.refl K K).prodCongr b.equivFun)
  let q := e.trans ((LinearEquiv.refl K K).prodCongr b'.equivFun)
  have hed : e d = (1, 0) := by
    apply Prod.ext
    · exact hd
    · apply Subtype.ext
      change d - B d d • d = 0
      simp [hd]
  refine ⟨p, q, fun _ => ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · simp [p, hed]
  · simp [q, hed]
  · intro x y
    let u := (e x).2
    let v := (e y).2
    have hu : B d u = 0 := u.property
    have hv : B d v = 0 := v.property
    have hx : (e x).1 • d + (u : E) = x := e.symm_apply_apply x
    have hy : (e y).1 • d + (v : E) = y := e.symm_apply_apply y
    have haux : (B.restrict U) u v = ∑ i, b.equivFun u i * b'.equivFun v i := by
      calc
        (B.restrict U) u v = (B.restrict U) v (∑ i, b.repr u i • b i) := by
          rw [b.sum_repr]; exact (hs.restrict U).eq u v
        _ = _ := by
          simp only [map_sum, map_smul, smul_eq_mul, Basis.equivFun_apply,
            b', LinearMap.BilinForm.dualBasis_repr_apply]
    change B x y = (e x).1 * (e y).1 + ∑ i, b.equivFun u i * b'.equivFun v i
    rw [← haux]
    conv_lhs => rw [← hx, ← hy]
    have hud : B u d = 0 := (hs.eq (u : E) d).trans hu
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hd, hud, hv, mul_one, mul_zero, add_zero, zero_add]
    rw [mul_comm]
    rfl

end

end

end FiniteFourier
end LinearAlgebra
end OAI
