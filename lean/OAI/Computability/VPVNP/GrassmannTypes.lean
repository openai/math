import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Basic.Real.Basic

/-!
# The binary Grassmannian and its distance classes

Section 5.1 uses the action of linear automorphisms on the ordered pairs of
middle-dimensional subspaces of a binary vector space. The type of a pair
is its sum dimension minus the common dimension of the subspaces.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

/-- The ambient binary vector space of dimension twice the plane dimension. -/
abbrev Space (m : ℕ) := Fin (2 * m) → ZMod 2

/-- Middle-dimensional subspaces of the ambient space. -/
def Plane (m : ℕ) := {U : Submodule (ZMod 2) (Space m) // Module.finrank (ZMod 2) U = m}

/-- The paper's type of an ordered pair, determined by its sum dimension. -/
def HasType {m : ℕ} (r : ℕ) (a b : Plane m) : Prop :=
  Module.finrank (ZMod 2) (a.val ⊔ b.val : Submodule (ZMod 2) (Space m)) = m + r

/-- All ordered pairs of type `r`. -/
def Pair (m r : ℕ) := {p : Plane m × Plane m // HasType r p.1 p.2}

/-- Linear automorphisms of the ambient binary space. -/
abbrev GL (m : ℕ) := Space m ≃ₗ[ZMod 2] Space m

instance (m : ℕ) : Finite (Plane m) :=
  Finite.of_injective (fun a : Plane m => (a.val : Set (Space m)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

instance (m r : ℕ) : Finite (Pair m r) :=
  Finite.of_injective _ (Subtype.val_injective (p := fun p : Plane m × Plane m =>
    HasType r p.1 p.2))

noncomputable instance (m : ℕ) : Fintype (Plane m) := Fintype.ofFinite _
noncomputable instance (m r : ℕ) : Fintype (Pair m r) := Fintype.ofFinite _

noncomputable instance (m : ℕ) : Fintype (GL m) :=
  @Fintype.ofFinite _ (Finite.of_injective (fun e : GL m => (e : Space m → Space m))
    DFunLike.coe_injective)

instance (m : ℕ) : MulAction (GL m) (Plane m) where
  smul e a := ⟨a.val.map e.toLinearMap, (e.finrank_map_eq a.val).trans a.property⟩
  one_smul a := Subtype.ext (Submodule.map_id _)
  mul_smul g h a := by
    apply Subtype.ext
    exact (Submodule.map_comp _ _ _)

theorem smul_plane_val {m : ℕ} (g : GL m) (a : Plane m) :
    (g • a).val = a.val.map g.toLinearMap := rfl

theorem HasType.smul {m r : ℕ} {a b : Plane m} (h : HasType r a b) (g : GL m) :
    HasType r (g • a) (g • b) := by
  unfold HasType
  rw [smul_plane_val, smul_plane_val, ← Submodule.map_sup, g.finrank_map_eq]
  exact h

instance (m r : ℕ) : MulAction (GL m) (Pair m r) where
  smul g p := ⟨(g • p.val.1, g • p.val.2), p.property.smul g⟩
  one_smul p := Subtype.ext (Prod.ext (one_smul _ p.val.1) (one_smul _ p.val.2))
  mul_smul g h p := Subtype.ext (Prod.ext (mul_smul g h p.val.1) (mul_smul g h p.val.2))

/-- The four side types and two diagonal types of a Grassmann quadrilateral. -/
structure IsSquare {m : ℕ} (r s : ℕ) (a b c d : Plane m) : Prop where
  ab : HasType r a b
  bc : HasType s b c
  cd : HasType r c d
  da : HasType s d a
  ac : HasType (r + s) a c
  bd : HasType (r + s) b d

/-- The uniform mean of an array over all ordered pairs of type `r`. -/
noncomputable def mean {m : ℕ} (D : Plane m → Plane m → ℝ) (r : ℕ) : ℝ :=
  (∑ p : Pair m r, D p.val.1 p.val.2) / Fintype.card (Pair m r)

end Grassmann

end VPVNP
end Computability
end OAI
