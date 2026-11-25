import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Ops
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Quotient
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Sum
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.AddLaws
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.MulLaws
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Distrib

/-! # The semiring of tensors up to mutual restriction

The sites, coefficient semiring, and finite coordinate spaces at each site
are arbitrary. Addition is the block direct sum and multiplication is the
tensor product grouped at each site. Both operations preserve local restriction.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v u w

variable {I : Type u} {K : Type w} [Fintype I] [CommSemiring K]

noncomputable section

instance : Add (TensorClass.{v} I K) where
  add := Quotient.map₂ Raw.add fun _ _ h _ _ g =>
    ⟨restrict_sum h.1 g.1, restrict_sum h.2 g.2⟩

instance : Mul (TensorClass.{v} I K) where
  mul := Quotient.map₂ Raw.mul fun _ _ h _ _ g =>
    ⟨Raw.mul_restricts h.1 g.1, Raw.mul_restricts h.2 g.2⟩

instance : Zero (TensorClass.{v} I K) := ⟨ofRaw (Raw.zero I K)⟩
instance : One (TensorClass.{v} I K) := ⟨ofRaw (Raw.one I K)⟩

@[simp] theorem ofRaw_add (X Y : Raw.{v} I K) : ofRaw (X.add Y) = ofRaw X + ofRaw Y := rfl

@[simp] theorem ofRaw_mul (X Y : Raw.{v} I K) : ofRaw (X.mul Y) = ofRaw X * ofRaw Y := rfl

@[simp] theorem ofRaw_zero : ofRaw (Raw.zero.{v} I K) = 0 := rfl

@[simp] theorem ofRaw_one : ofRaw (Raw.one.{v} I K) = 1 := rfl

private theorem class_add_comm (X Y : TensorClass.{v} I K) : X + Y = Y + X :=
  Quotient.inductionOn₂ X Y fun x y => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.sumComm _ _) (sumCoeff_comm x.coeff y.coeff)

private theorem class_zero_add (X : TensorClass.{v} I K) : 0 + X = X := by
  let (i : I) : IsEmpty ((Raw.zero.{v} I K).Leg i) := inferInstanceAs (IsEmpty PEmpty)
  exact
  Quotient.inductionOn X fun x => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.emptySum _ _) (zero_sumCoeff x.coeff)

private theorem class_mul_comm (X Y : TensorClass.{v} I K) : X * Y = Y * X :=
  Quotient.inductionOn₂ X Y fun x y => Quotient.sound (x.mul_comm_equivalent y)

private theorem class_one_mul (X : TensorClass.{v} I K) : 1 * X = X :=
  Quotient.inductionOn X fun x => Quotient.sound (x.one_mul_equivalent)

variable [Nonempty I]

private theorem class_zero_mul (X : TensorClass.{v} I K) : 0 * X = 0 :=
  Quotient.inductionOn X fun x => Quotient.sound (x.zero_mul_equivalent)

private theorem class_left_distrib (X Y Z : TensorClass.{v} I K) :
    X * (Y + Z) = X * Y + X * Z :=
  Quotient.inductionOn₃ X Y Z fun x y z => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.prodSumDistrib _ _ _)
      (sumCoeff_product_distrib x.coeff y.coeff z.coeff)

/-- The restriction classes form the tensor semiring of the manuscript. -/
instance : CommSemiring (TensorClass.{v} I K) where
  add_assoc X Y Z := Quotient.inductionOn₃ X Y Z fun x y z => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.sumAssoc _ _ _) (sumCoeff_assoc x.coeff y.coeff z.coeff)
  add_comm := class_add_comm
  zero_add := class_zero_add
  add_zero X := (class_add_comm X 0).trans (class_zero_add X)
  nsmul := nsmulRec
  mul_assoc X Y Z := Quotient.inductionOn₃ X Y Z fun x y z =>
    Quotient.sound (x.mul_assoc_equivalent y z)
  mul_comm := class_mul_comm
  one_mul := class_one_mul
  mul_one X := (class_mul_comm X 1).trans (class_one_mul X)
  zero_mul := class_zero_mul
  mul_zero X := (class_mul_comm X 0).trans (class_zero_mul X)
  left_distrib := class_left_distrib
  right_distrib X Y Z := by rw [class_mul_comm, class_left_distrib, class_mul_comm Z X, class_mul_comm Z Y]

omit [Nonempty I] in
/-- Both arguments of block direct sum are monotone under restriction. -/
theorem add_mono {X Y U V : TensorClass.{v} I K} (h : X ≤ Y) (g : U ≤ V) :
    X + U ≤ Y + V := by
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  induction U using Quotient.inductionOn
  induction V using Quotient.inductionOn
  exact restrict_sum h g

omit [Nonempty I] in
/-- Both arguments of tensor product are monotone under restriction. -/
theorem mul_mono {X Y U V : TensorClass.{v} I K} (h : X ≤ Y) (g : U ≤ V) :
    X * U ≤ Y * V := by
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  induction U using Quotient.inductionOn
  induction V using Quotient.inductionOn
  exact Raw.mul_restricts h g

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
