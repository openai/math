import OAI.ThreeFlat.ExpanderBasic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod

namespace OAI
/-! # Uniform restrictions of random binary linear maps -/

noncomputable section
namespace Hierarchy.NonlinearExpanders

open ThreeFlat.Expander

/-- A surjective additive homomorphism pushes the uniform measure forward
to the uniform measure, because every fiber is a translate of the kernel. -/
theorem avg_surjective_addHom {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] (L : A →+ B) (surj : Function.Surjective L) (h : B → ℝ) :
    avg (fun a => h (L a)) = avg h := by
  classical
  choose r hr using surj
  let K := {a : A // L a = 0}
  let : Fintype K := Fintype.ofFinite _
  let : Nonempty K := ⟨⟨0,map_zero _⟩⟩
  let e : A ≃ B × K := {
    toFun := fun a => (L a, ⟨a-r (L a), by simp [hr]⟩)
    invFun := fun p => p.2.1 + r p.1
    left_inv := fun a => sub_add_cancel _ _
    right_inv := by
      rintro ⟨b,⟨k,hk⟩⟩
      apply Prod.ext
      · simp [hk,hr]
      · apply Subtype.ext
        simp [hk,hr] }
  calc
    _ = avg (fun p : B × K => h p.1) := avg_equiv e _
    _ = _ := by rw [avg_prod (fun b (_ : K) => h b)]; simp

variable {U V E : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup E]
  [Module (ZMod 2) U] [Module (ZMod 2) V] [Module (ZMod 2) E]

/-- The restriction of a uniform random linear map to an injectively
embedded subspace is uniform over all linear maps on that subspace. -/
theorem avg_restrict_linear [Fintype (V →ₗ[ZMod 2] E)] [Fintype (U →ₗ[ZMod 2] E)]
    (f : U →ₗ[ZMod 2] V) (inj : Function.Injective f)
    (h : (U →ₗ[ZMod 2] E) → ℝ) :
    avg (fun g : V →ₗ[ZMod 2] E => h (g.comp f)) = avg h := by
  let L : (V →ₗ[ZMod 2] E) →+ (U →ₗ[ZMod 2] E) :=
    { toFun := fun g => g.comp f
      map_add' := fun _ _ => rfl
      map_zero' := rfl }
  apply avg_surjective_addHom L _ h
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr inj)
  intro k
  exact ⟨k.comp g, by change (k.comp g).comp f = k; rw [LinearMap.comp_assoc, hg, k.comp_id]⟩

/-- Label all assignments of a binary subspace by a finite set of the
corresponding size. A plane keeps the same labels in all of its adjacencies. -/
def homLabels (U : Type*) [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] {r n : ℕ} (h : Module.finrank (ZMod 2) U = r) :
    (U →ₗ[ZMod 2] (Fin n → ZMod 2)) ≃ Fin ((2^n)^r) :=
  ((Module.finBasisOfFinrankEq (ZMod 2) U h).constr (ZMod 2)).symm.toEquiv.trans
    (Fintype.equivFinOfCardEq (by simp [ZMod.card]))

end Hierarchy.NonlinearExpanders

end
end OAI
