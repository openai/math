import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Uniform sampling through a surjective additive map

In Section 5.2, evaluation of a random linear map on a frame is a surjective
additive homomorphism. Translation invariance of finite group averages shows
that its image is uniformly distributed, including for simultaneous evaluation
on a frame spanning the two adjacent planes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

/-- A surjective additive homomorphism carries the uniform distribution of the
finite domain to the uniform distribution of the codomain. -/
theorem uniformAverage_comp_surjective {A B : Type*} [AddGroup A] [AddGroup B]
    [Fintype A] [Fintype B] (f : A →+ B) (hf : Function.Surjective f) (g : B → ℝ) :
    (∑ a : A, g (f a)) / Fintype.card A = (∑ b : B, g b) / Fintype.card B := by
  have ha (b : B) : (∑ a : A, g (f a + b)) = ∑ a : A, g (f a) := by
    obtain ⟨t, rfl⟩ := hf b
    simp_rw [← map_add]
    exact Equiv.sum_comp (Equiv.addRight t) (fun a : A ↦ g (f a))
  have hb (a : A) : (∑ b : B, g (f a + b)) = ∑ b : B, g b :=
    Equiv.sum_comp (Equiv.addLeft (f a)) g
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).2
  calc
    _ = ∑ b : B, ∑ a : A, g (f a + b) := by simp_rw [ha]; simp [mul_comm]
    _ = ∑ a : A, ∑ b : B, g (f a + b) := Finset.sum_comm
    _ = _ := by simp_rw [hb]; simp [mul_comm]

variable {K V E ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup E] [Module K E]

/-- Independent columns can be assigned arbitrary values by a linear map. -/
theorem frame_eval_surjective (w : ι → V) (hw : LinearIndependent K w) :
    Function.Surjective (fun (f : V →ₗ[K] E) (j : ι) ↦ f (w j)) := by
  obtain ⟨r, hr⟩ := (Finsupp.linearCombination K w).exists_leftInverse_of_injective
    (linearIndependent_iff_ker.mp hw)
  intro z
  refine ⟨(Finsupp.linearCombination K z).comp r, ?_⟩
  funext j
  have h := LinearMap.congr_fun hr (Finsupp.single j 1)
  simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
    LinearMap.id_coe, id_eq] at h
  simp only [LinearMap.comp_apply, h, Finsupp.linearCombination_single, one_smul]

/-- The joint images of any independent frame under a uniform linear map
have the uniform distribution on all tuples of target values. -/
theorem uniformAverage_frame_eval [Fintype ι] [DecidableEq ι] [Fintype E] [Fintype (V →ₗ[K] E)]
    (w : ι → V) (hw : LinearIndependent K w) (g : (ι → E) → ℝ) :
    (∑ f : V →ₗ[K] E, g (fun j ↦ f (w j))) / Fintype.card (V →ₗ[K] E) =
      (∑ z : ι → E, g z) / Fintype.card (ι → E) := by
  let f := LinearMap.pi (fun j ↦ LinearMap.applyₗ (R := K) (M₂ := E) (w j))
  exact uniformAverage_comp_surjective f.toAddMonoidHom (frame_eval_surjective w hw) g

end SpectralGeometry

end VPVNP
end Computability
end OAI
