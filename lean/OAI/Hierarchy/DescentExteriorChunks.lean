import OAI.Hierarchy.DescentExteriorShears
import OAI.Hierarchy.DescentGLConditional

namespace OAI
/-! # The actual three chunk permutations of each exterior stack array -/
namespace Hierarchy.DescentExterior
open DescentGL
open scoped Classical BigOperators
noncomputable section

/-- Exchange the low chunk-coordinate block and the designated high block. -/
def flip {A T : Type} : (A×(A×T)) ≃ (A×(A×T)) where
  toFun x := (x.2.1,x.1,x.2.2)
  invFun x := (x.2.1,x.1,x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def shift {A : Type} [AddGroup A] (u : A) : A≃A where
  toFun a := a+u
  invFun a := a-u
  left_inv _ := add_sub_cancel_right ..
  right_inv _ := sub_add_cancel ..

variable {F U T : Type} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup T] [Module F T]

def lowerChunks (C : U→ₗ[F](U×T)) : ChunkPermutation (U×T) U where
  row :=
    { toFun := fun y=>(y.1,y.2+(C y.1).2)
      invFun := fun y=>(y.1,y.2-(C y.1).2)
      left_inv := by intro y; simp
      right_inv := by intro y; simp }
  slot y:=shift (C y.1).1

theorem lower_chunks_apply (C : U→ₗ[F](U×T)) (x : U×(U×T)) :
    flip ((lowerChunks C).apply (flip x))=lower C x := rfl

/-- Every one of the three passes performs one permutation of whole rows
and a separate permutation inside each row. The changes of grouping between
the passes are fixed exchanges of two coordinate blocks. -/
theorem physical_factors [Finite U] [Finite T] [FiniteDimensional F U] [FiniteDimensional F T]
    (M : (U×(U×T)) ≃ₗ[F] (U×(U×T))) :
    ∃ Q C L : ChunkPermutation (U×T) U,
      ∀x,M x=L.apply (flip (C.apply (flip (Q.apply x)))) := by
  obtain ⟨Q,C,L,top,eq⟩:=factor M
  have up : IsUpper (upper L) := by intro _;rfl
  refine ⟨chunks Q top,lowerChunks C,chunks (upper L) up,?_⟩
  intro x
  rw [chunks_apply,chunks_apply,lower_chunks_apply,eq]

def castBits {n m : ℕ} (h : n=m) : Bits n ≃ₗ[ZMod 2] Bits m :=
  h ▸ LinearEquiv.refl _ _

/-- Colony indices store the most significant bit first. The last j
coordinates therefore enumerate the stacks in a contiguous input chunk. -/
def coords (j r : ℕ) : Bits (j+(j+r)) ≃ₗ[ZMod 2] (Bits j×(Bits j×Bits r)) :=
  (((castBits (Nat.add_comm j (j+r))).trans (splitRows (j+r) j)).trans
    (LinearEquiv.prodComm (ZMod 2) _ _)).trans
    ((LinearEquiv.refl _ _).prodCongr (splitRows j r))

abbrev Rows (j r : ℕ) := Bits j × Bits r
abbrev Stage (j r : ℕ) := ChunkPermutation (Rows j r) (Bits j)

theorem binary_factors (j r : ℕ) (M : Layout (j+(j+r))) :
    ∃ a b c : Stage j r, ∀x, coords j r (M x) =
      c.apply (flip (b.apply (flip (a.apply (coords j r x))))) := by
  let g:=coords j r
  obtain ⟨a,b,c,eq⟩:=physical_factors ((g.symm.trans M).trans g)
  refine ⟨a,b,c,fun x=>?_⟩
  simpa only [LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,g] using eq (g x)

/-- Literal row order changes needed between the second and third passes. -/
structure Plan (j r : ℕ) where
  first : Stage j r
  middle : Stage j r
  last : Stage j r

def plan {j r : ℕ} (M : Layout (j+(j+r))) : Plan j r := by
  classical
  let a:=Classical.choose (binary_factors j r M)
  let ha:=Classical.choose_spec (binary_factors j r M)
  let b:=Classical.choose ha
  let hb:=Classical.choose_spec ha
  exact ⟨a,b,Classical.choose hb⟩

theorem plan_apply {j r : ℕ} (M : Layout (j+(j+r))) (x : Bits (j+(j+r))) :
    coords j r (M x)=(plan M).last.apply (flip ((plan M).middle.apply
      (flip ((plan M).first.apply (coords j r x))))) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (binary_factors j r M))) x

theorem rows_card (j r : ℕ) : Fintype.card (Rows j r)=2^(j+r) := by
  simp [Rows,Bits,pow_add]

theorem slots_card (j : ℕ) : Fintype.card (Bits j)=2^j := by simp [Bits]

end
end Hierarchy.DescentExterior

end OAI
