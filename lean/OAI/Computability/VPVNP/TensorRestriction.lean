import OAI.Computability.VPVNP.WireTensor

/-!
# Tensor classes modulo mutual restriction

Each class retains its concrete restriction comparisons. The smaller class
is the demand and the larger class is the supply. Direct sums and products
descend to the quotient because independent local maps act on both factors.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

universe u v

variable (k : Type u) (J : Type v) [Field k] [Fintype J]

/-- Identifying exactly those tensors that restrict to each other. -/
def restrictionSetoid : Setoid (Tensor.{u,v,0} k J) where
  r T U := Restricts T U ∧ Restricts U T
  iseqv := ⟨fun T => ⟨.refl T, .refl T⟩, fun h => h.symm,
    fun h g => ⟨h.1.trans g.1, g.2.trans h.2⟩⟩

/-- The restriction classes used to form the semiring of Section 2. -/
def RestrictionClass := Quotient (restrictionSetoid k J)

namespace RestrictionClass

variable {k J}

/-- Map a concrete tensor to its equivalence class under mutual restriction by local linear
maps. -/
def ofTensor (T : Tensor.{u,v,0} k J) : RestrictionClass k J :=
  Quotient.mk (restrictionSetoid k J) T

theorem ofTensor_eq_iff (T U : Tensor.{u,v,0} k J) :
    ofTensor T = ofTensor U ↔ Restricts T U ∧ Restricts U T :=
  Quotient.eq

theorem ofTensor_surjective : Function.Surjective (ofTensor (k := k) (J := J)) :=
  Quotient.exists_rep

instance : LE (RestrictionClass k J) where
  le x y := Quotient.liftOn₂ x y (fun T U => Restricts U T) <| by
    intro a b c d hab hcd
    exact propext ⟨fun h => hcd.2.trans (h.trans hab.1), fun h => hcd.1.trans (h.trans hab.2)⟩

theorem ofTensor_le_iff (T U : Tensor.{u,v,0} k J) :
    ofTensor T ≤ ofTensor U ↔ Restricts U T := Iff.rfl

instance : PartialOrder (RestrictionClass k J) where
  le_refl x := Quotient.inductionOn x Restricts.refl
  le_trans x y z := Quotient.inductionOn₃ x y z fun _ _ _ h g => Restricts.trans g h
  le_antisymm x y := Quotient.inductionOn₂ x y fun _ _ h g => Quotient.sound ⟨g, h⟩

noncomputable instance : Add (RestrictionClass k J) where
  add := Quotient.map₂ directSum fun _ _ h _ _ g =>
    ⟨directSum_restricts h.1 g.1, directSum_restricts h.2 g.2⟩

instance : Mul (RestrictionClass k J) where
  mul := Quotient.map₂ tensorProduct fun _ _ h _ _ g =>
    ⟨h.1.tensorProduct g.1, h.2.tensorProduct g.2⟩

noncomputable instance : Zero (RestrictionClass k J) := ⟨ofTensor (diagonal (Fin 0))⟩

instance : One (RestrictionClass k J) := ⟨ofTensor unit⟩

@[simp] theorem ofTensor_directSum (T U : Tensor.{u,v,0} k J) :
    ofTensor (directSum T U) = ofTensor T + ofTensor U := rfl

@[simp] theorem ofTensor_tensorProduct (T U : Tensor.{u,v,0} k J) :
    ofTensor (tensorProduct T U) = ofTensor T * ofTensor U := rfl

@[simp] theorem ofTensor_diagonal_zero : ofTensor (diagonal (Fin 0)) = (0 : RestrictionClass k J) :=
  rfl

@[simp] theorem ofTensor_unit : ofTensor unit = (1 : RestrictionClass k J) := rfl

end RestrictionClass
end WireTensor

end VPVNP
end Computability
end OAI
