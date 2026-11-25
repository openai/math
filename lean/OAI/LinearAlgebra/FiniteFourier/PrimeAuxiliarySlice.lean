import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Coordinates for a subspace in the auxiliary slice of an axis chart

If a subspace lies in the zero axis slice, projection onto the auxiliary
factor embeds it there. A complement in that factor gives coordinates that
keep both the axis value and the original subspace representatives.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

variable {K E A : Type*} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup A] [Module K A]

/-- A choice of auxiliary complement together with coordinates respecting the given subspace. -/
structure AuxiliarySlice (e : E ≃ₗ[K] K × A) (H : Submodule K E) where
  C : Submodule K A
  split : (H × C) ≃ₗ[K] A
  split_zero (u : H) : split (u, 0) = (e u).2
  axis_zero (u : H) : (e u).1 = 0

/-- Projecting a subspace of the zero slice to the auxiliary factor loses no coordinates. -/
def auxiliarySlice (e : E ≃ₗ[K] K × A) (H : Submodule K E) (h : ∀ x ∈ H, (e x).1 = 0) :
    AuxiliarySlice e H := Classical.choice <| by
  let f := (LinearMap.snd K K A).comp (e.toLinearMap.comp H.subtype)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact e.injective (Prod.ext ((h x x.2).trans (h y y.2).symm) hxy)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range f)
  let g := ((LinearEquiv.ofInjective f hf).prodCongr (LinearEquiv.refl K C)).trans
    ((LinearMap.range f).prodEquivOfIsCompl C hC)
  refine ⟨⟨C, g, ?_, fun u => h u u.2⟩⟩
  intro u
  change f u + 0 = (e u).2
  exact add_zero _

namespace AuxiliarySlice

variable {e : E ≃ₗ[K] K × A} {H : Submodule K E} (S : AuxiliarySlice e H)

/-- Coordinates adapted to cosets of the subspace and to the scalar axis. -/
def chart : (H × (K × S.C)) ≃ₗ[K] E :=
  (LinearEquiv.prodAssoc K H K S.C).symm ≪≫ₗ
    ((LinearEquiv.prodComm K H K).prodCongr (LinearEquiv.refl K S.C)) ≪≫ₗ
    (LinearEquiv.prodAssoc K K H S.C) ≪≫ₗ
    ((LinearEquiv.refl K K).prodCongr S.split) ≪≫ₗ e.symm

theorem chart_apply (u : H) (k : K) (c : S.C) :
    S.chart (u, (k, c)) = e.symm (k, S.split (u, c)) := rfl

@[simp] theorem chart_zero (u : H) : S.chart (u, 0) = u := by
  rw [show (0 : K × S.C) = (0, 0) from rfl, S.chart_apply, S.split_zero]
  apply e.symm_apply_eq.mpr
  exact Prod.ext (S.axis_zero u).symm rfl

theorem finrank_eq [FiniteDimensional K E] [FiniteDimensional K A] :
    Module.finrank K H + Module.finrank K S.C = Module.finrank K A := by
  rw [← Module.finrank_prod]
  exact S.split.finrank_eq

end AuxiliarySlice
end

end

end FiniteFourier
end LinearAlgebra
end OAI
