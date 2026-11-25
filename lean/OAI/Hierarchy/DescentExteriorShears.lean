import OAI.Hierarchy.DescentExteriorPivot
import Mathlib.LinearAlgebra.Prod

namespace OAI
/-! # Three linear factors for the exterior chunk permutation -/
namespace Hierarchy.DescentExterior
open scoped Classical
noncomputable section

variable {F U V : Type} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]

/-- Add a linear function of the unchanged high coordinates to the low coordinates. -/
def upper (L : V→ₗ[F]U) : (U×V) ≃ₗ[F] (U×V) where
  toFun a := (a.1+L a.2,a.2)
  invFun a := (a.1-L a.2,a.2)
  left_inv a := by simp
  right_inv a := by simp
  map_add' a b := by ext <;> simp [add_comm,add_left_comm,add_assoc]
  map_smul' c a := by ext <;> simp [smul_add]

def lower (C : U→ₗ[F]V) : (U×V) ≃ₗ[F] (U×V) where
  toFun a := (a.1,a.2+C a.1)
  invFun a := (a.1,a.2-C a.1)
  left_inv a := by simp
  right_inv a := by simp
  map_add' a b := by ext <;> simp [add_comm,add_left_comm,add_assoc]
  map_smul' c a := by ext <;> simp [smul_add]

def IsUpper (Q : (U×V)≃ₗ[F](U×V)) := ∀u : U,(Q (u,0)).2=0

def lowBlock (M : (U×V)≃ₗ[F](U×V)) :=
  (LinearMap.fst F U V).comp (M.toLinearMap.comp (LinearMap.inl F U V))

def crossBlock (M : (U×V)≃ₗ[F](U×V)) :=
  (LinearMap.snd F U V).comp (M.toLinearMap.comp (LinearMap.inl F U V))

/-- The factor nearest the input is upper triangular, the middle factor
is a genuine lower shear, and the last factor is an upper shear. -/
theorem factor [FiniteDimensional F U] [FiniteDimensional F V] (M : (U×V)≃ₗ[F](U×V)) :
    ∃ (Q : (U×V)≃ₗ[F](U×V)) (C : U→ₗ[F]V) (L : V→ₗ[F]U),
      IsUpper Q ∧ ∀x,M x=upper L (lower C (Q x)) := by
  let A:=lowBlock M
  let B:=crossBlock M
  have independent (u : U) (ha : A u=0) (hb : B u=0) : u=0 := by
    have hz : M (u,0)=M 0 := by rw [map_zero]; exact Prod.ext ha hb
    exact congrArg Prod.fst (M.injective hz)
  obtain ⟨L,good⟩:=DescentExteriorPivot.exists_pivot A B independent
  let P : U≃ₗ[F]U := LinearEquiv.ofBijective (A+L.comp B) good
  let C : U→ₗ[F]V := B.comp P.symm.toLinearMap
  have corrected (u : U) : C (P u)=B u := by simp [C]
  let Q := (M.trans (upper L)).trans (lower (-C))
  refine ⟨Q,C,-L,?_,?_⟩
  · intro u
    change B u+(-C) (P u)=0
    simp only [LinearMap.neg_apply,corrected,add_neg_cancel]
  · intro x
    let a:=M x
    change a=(a.1+L a.2+(-L) (a.2+(-C) (a.1+L a.2)+C (a.1+L a.2)),
      a.2+(-C) (a.1+L a.2)+C (a.1+L a.2))
    have undo : a.2+(-C) (a.1+L a.2)+C (a.1+L a.2)=a.2 := by
      rw [LinearMap.neg_apply]
      abel
    rw [undo,LinearMap.neg_apply]
    exact Prod.ext (by change a.1=a.1+L a.2+ -(L a.2); abel) rfl

/-- Each row moves to a single destination row. Its elements get a
permutation depending only on the source row. -/
structure ChunkPermutation (A B : Type) where
  row : A ≃ A
  slot : A → B ≃ B

def ChunkPermutation.apply {A B : Type} (c : ChunkPermutation A B) (x : B × A) : B × A :=
  (c.slot x.2 x.1,c.row x.2)

theorem upper_high (Q : (U×V)≃ₗ[F](U×V)) (ok : IsUpper Q) (u : U) (v : V) :
    (Q (u,v)).2=(Q (0,v)).2 := by
  have hx : (u,v)=(u,0)+(0,v) := by simp
  rw [hx,map_add]
  change (Q (u,0)).2+(Q (0,v)).2=_
  rw [ok,zero_add]

def chunks [Finite U] [Finite V] (Q : (U×V)≃ₗ[F](U×V)) (ok : IsUpper Q) :
    ChunkPermutation V U where
  row := Equiv.ofBijective (fun v : V=>(Q (0,v)).2) (Finite.surjective_iff_bijective.mp (by
    intro v
    obtain ⟨a,ha⟩:=Q.surjective (0,v)
    exact ⟨a.2,(upper_high Q ok a.1 a.2).symm.trans (congrArg Prod.snd ha)⟩))
  slot v := Equiv.ofBijective (fun u : U=>(Q (u,v)).1) (Finite.injective_iff_bijective.mp (by
    intro u u' h
    have eq : Q (u,v)=Q (u',v) :=
      Prod.ext h ((upper_high Q ok u v).trans (upper_high Q ok u' v).symm)
    exact congrArg Prod.fst (Q.injective eq)))

theorem chunks_apply [Finite U] [Finite V] (Q : (U×V)≃ₗ[F](U×V)) (ok : IsUpper Q) (x : U×V) :
    (chunks Q ok).apply x=Q x := Prod.ext rfl (upper_high Q ok x.1 x.2).symm

end
end Hierarchy.DescentExterior

end OAI
