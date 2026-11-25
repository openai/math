import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace OAI
/-! # Repairing a singular block using the other block of an injective column -/

namespace Hierarchy.DescentExteriorPivot

variable {F U V : Type*} [Field F] [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V] [FiniteDimensional F U]

/-- An injective block column admits an invertible upper block after a single
upper block shear. The lower block can have any dimension. -/
theorem exists_pivot (A : U →ₗ[F] U) (C : U →ₗ[F] V)
    (joint : ∀ u, A u=0 → C u=0 → u=0) :
    ∃ L : V →ₗ[F] U, Function.Bijective (A+L.comp C) := by
  classical
  let a : LinearMap.ker C →ₗ[F] U := A.comp (LinearMap.ker C).subtype
  have inj : Function.Injective a := by
    intro x y h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply joint
    · exact (map_sub A (x:U) y).trans (sub_eq_zero.mpr h)
    · rw [map_sub,show C (x:U)=0 from x.property,show C (y:U)=0 from y.property,sub_self]
  obtain ⟨g,hg⟩ := Submodule.exists_linearEquiv_restrict_eq (LinearEquiv.ofInjective a inj)
  let d : U →ₗ[F] U := g.toLinearMap-A
  have kill : LinearMap.ker C ≤ LinearMap.ker d := by
    intro x hx
    have same : A x=g x := hg ⟨x,hx⟩
    exact sub_eq_zero.mpr same.symm
  let q := (LinearMap.ker C).liftQ d kill
  let part : LinearMap.range C →ₗ[F] U := q.comp C.quotKerEquivRange.symm.toLinearMap
  obtain ⟨L,ext⟩ := part.exists_extend
  refine ⟨L,?_⟩
  have eq : A+L.comp C=g.toLinearMap := by
    ext x
    let z : LinearMap.range C := ⟨C x,⟨x,rfl⟩⟩
    have hz : L (C x)=part z := LinearMap.congr_fun ext z
    have val : part z=d x := by
      change q (C.quotKerEquivRange.symm ⟨C x,_⟩)=d x
      exact congrArg (fun v=>q v) (C.quotKerEquivRange_symm_apply_image x ⟨x,rfl⟩)
    change A x+L (C x)=g x
    rw [hz,val]
    change A x+(g x-A x)=g x
    rw [add_comm,sub_add_cancel]
  rw [eq]
  exact g.bijective


end Hierarchy.DescentExteriorPivot

end OAI
