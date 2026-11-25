import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Blocks
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Ring.Defs

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# The semiring of actual finite tensors

Every law is obtained from an explicit coordinate relabeling. The quotient
identifies mutual restriction, not numerical ranks or an abstract tensor model.
-/

open OAI.MatrixMultiplication.Foundation
open OAI.LinearAlgebra.MatrixExponent.Integral.Upper.CoefficientTensor
open scoped NNReal

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass

noncomputable instance : Add TensorClass where
  add A B := Quotient.liftOn₂ A B
    (fun a b => ofTensor (blockSum a.coeff b.coeff)) (by
      intro a b a' b' ha hb
      exact ofTensor_eq (ha.1.blockSum hb.1) (ha.2.blockSum hb.2))

noncomputable instance : Mul TensorClass where
  mul A B := Quotient.liftOn₂ A B
    (fun a b => ofTensor (Tensor.product a.coeff b.coeff)) (by
      intro a b a' b' ha hb
      exact ofTensor_eq (ha.1.product hb.1) (ha.2.product hb.2))

def emptyTensor : Tensor O Empty Empty Empty := fun x => nomatch x
def unitTensor : Tensor O PUnit.{1} PUnit.{1} PUnit.{1} := fun _ _ _ => 1

noncomputable instance : Zero TensorClass := ⟨ofTensor emptyTensor⟩
noncomputable instance : One TensorClass := ⟨ofTensor unitTensor⟩

theorem ofTensor_add {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor O X Y Z) (S : Tensor O U V W) :
    ofTensor T + ofTensor S = ofTensor (blockSum T S) := by
  apply ofTensor_eq
  · exact (TensorRep.ofTensor_restricts T).blockSum (TensorRep.ofTensor_restricts S)
  · exact (TensorRep.restricts_ofTensor T).blockSum (TensorRep.restricts_ofTensor S)

theorem ofTensor_mul {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor O X Y Z) (S : Tensor O U V W) :
    ofTensor T * ofTensor S = ofTensor (Tensor.product T S) := by
  apply ofTensor_eq
  · exact (TensorRep.ofTensor_restricts T).product (TensorRep.ofTensor_restricts S)
  · exact (TensorRep.restricts_ofTensor T).product (TensorRep.restricts_ofTensor S)

private theorem add_comm_aux (A B : TensorClass) : A + B = B + A := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      change ofRep a + ofRep b = ofRep b + ofRep a
      rw [← ofTensor_coeff a, ← ofTensor_coeff b, ofTensor_add, ofTensor_add]
      have heq : Tensor.pullback (Equiv.sumComm _ _) (Equiv.sumComm _ _)
          (Equiv.sumComm _ _) (blockSum b.coeff a.coeff) = blockSum a.coeff b.coeff := by
        funext x y z
        rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;> rfl
      rw [← heq]
      exact ofTensor_pullback_equiv _ _ _ _

private theorem add_assoc_aux (A B C : TensorClass) : (A + B) + C = A + (B + C) := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      induction C using Quotient.inductionOn with | h c =>
        change (ofRep a + ofRep b) + ofRep c = ofRep a + (ofRep b + ofRep c)
        rw [← ofTensor_coeff a, ← ofTensor_coeff b, ← ofTensor_coeff c]
        simp only [ofTensor_add]
        have heq : Tensor.pullback (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _)
            (Equiv.sumAssoc _ _ _) (blockSum a.coeff (blockSum b.coeff c.coeff)) =
            blockSum (blockSum a.coeff b.coeff) c.coeff := by
          funext x y z
          rcases x with (x | x) | x <;> rcases y with (y | y) | y <;>
            rcases z with (z | z) | z <;> rfl
        rw [← heq]
        exact ofTensor_pullback_equiv _ _ _ _

private theorem zero_add_aux (A : TensorClass) : 0 + A = A := by
  induction A using Quotient.inductionOn with | h a =>
    change 0 + ofRep a = ofRep a
    rw [← ofTensor_coeff a]
    change ofTensor emptyTensor + ofTensor a.coeff = _
    rw [ofTensor_add]
    have heq : Tensor.pullback (Equiv.emptySum Empty _) (Equiv.emptySum Empty _)
        (Equiv.emptySum Empty _) a.coeff = blockSum emptyTensor a.coeff := by
      funext x y z
      rcases x with x | x
      · exact x.elim
      rcases y with y | y
      · exact y.elim
      rcases z with z | z
      · exact z.elim
      rfl
    rw [← heq]
    exact ofTensor_pullback_equiv _ _ _ _

private theorem mul_comm_aux (A B : TensorClass) : A * B = B * A := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      change ofRep a * ofRep b = ofRep b * ofRep a
      rw [← ofTensor_coeff a, ← ofTensor_coeff b, ofTensor_mul, ofTensor_mul]
      have heq : Tensor.pullback (Equiv.prodComm _ _) (Equiv.prodComm _ _)
          (Equiv.prodComm _ _) (Tensor.product b.coeff a.coeff) =
          Tensor.product a.coeff b.coeff := by
        funext x y z
        exact mul_comm _ _
      rw [← heq]
      exact ofTensor_pullback_equiv _ _ _ _

private theorem mul_assoc_aux (A B C : TensorClass) : (A * B) * C = A * (B * C) := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      induction C using Quotient.inductionOn with | h c =>
        change (ofRep a * ofRep b) * ofRep c = ofRep a * (ofRep b * ofRep c)
        rw [← ofTensor_coeff a, ← ofTensor_coeff b, ← ofTensor_coeff c]
        simp only [ofTensor_mul]
        have heq : Tensor.pullback (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
            (Equiv.prodAssoc _ _ _) (Tensor.product a.coeff (Tensor.product b.coeff c.coeff)) =
            Tensor.product (Tensor.product a.coeff b.coeff) c.coeff := by
          funext x y z
          exact (mul_assoc _ _ _).symm
        rw [← heq]
        exact ofTensor_pullback_equiv _ _ _ _

private theorem one_mul_aux (A : TensorClass) : 1 * A = A := by
  induction A using Quotient.inductionOn with | h a =>
    change 1 * ofRep a = ofRep a
    rw [← ofTensor_coeff a]
    change ofTensor unitTensor * ofTensor a.coeff = _
    rw [ofTensor_mul]
    have heq : Tensor.pullback (Equiv.punitProd _) (Equiv.punitProd _)
        (Equiv.punitProd _) a.coeff = Tensor.product unitTensor a.coeff := by
      funext x y z
      exact (one_mul _).symm
    rw [← heq]
    exact ofTensor_pullback_equiv _ _ _ _

private theorem zero_mul_aux (A : TensorClass) : 0 * A = 0 := by
  induction A using Quotient.inductionOn with | h a =>
    change 0 * ofRep a = 0
    rw [← ofTensor_coeff a]
    change ofTensor emptyTensor * ofTensor a.coeff = ofTensor emptyTensor
    rw [ofTensor_mul]
    apply ofTensor_eq
    · refine ⟨fun x => x.elim, fun y => y.elim, fun z => z.elim, ?_⟩
      funext x
      exact x.elim
    · refine ⟨fun x => x.1.elim, fun y => y.1.elim, fun z => z.1.elim, ?_⟩
      funext x
      exact x.1.elim

private theorem left_distrib_aux (A B C : TensorClass) : A * (B + C) = A * B + A * C := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      induction C using Quotient.inductionOn with | h c =>
        change ofRep a * (ofRep b + ofRep c) = ofRep a * ofRep b + ofRep a * ofRep c
        rw [← ofTensor_coeff a, ← ofTensor_coeff b, ← ofTensor_coeff c]
        simp only [ofTensor_add, ofTensor_mul]
        have heq : Tensor.pullback (Equiv.prodSumDistrib _ _ _) (Equiv.prodSumDistrib _ _ _)
            (Equiv.prodSumDistrib _ _ _)
            (blockSum (Tensor.product a.coeff b.coeff) (Tensor.product a.coeff c.coeff)) =
            Tensor.product a.coeff (blockSum b.coeff c.coeff) := by
          funext x y z
          rcases x with ⟨x, x'⟩
          rcases y with ⟨y, y'⟩
          rcases z with ⟨z, z'⟩
          rcases x' with x' | x' <;> rcases y' with y' | y' <;> rcases z' with z' | z' <;>
            simp [Tensor.pullback, Tensor.product, blockSum, Equiv.prodSumDistrib]
        rw [← heq]
        exact ofTensor_pullback_equiv _ _ _ _

noncomputable instance : CommSemiring TensorClass where
  add := (· + ·)
  mul := (· * ·)
  zero := 0
  one := 1
  nsmul := nsmulRec
  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl
  add_assoc := add_assoc_aux
  add_comm := add_comm_aux
  zero_add := zero_add_aux
  add_zero A := by rw [add_comm_aux]; exact zero_add_aux A
  mul_assoc := mul_assoc_aux
  mul_comm := mul_comm_aux
  one_mul := one_mul_aux
  mul_one A := by rw [mul_comm_aux]; exact one_mul_aux A
  zero_mul := zero_mul_aux
  mul_zero A := by rw [mul_comm_aux]; exact zero_mul_aux A
  left_distrib := left_distrib_aux
  right_distrib A B C := by
    rw [mul_comm_aux, left_distrib_aux, mul_comm_aux C A, mul_comm_aux C B]

theorem add_mono {A B C D : TensorClass} (hAB : A ≤ B) (hCD : C ≤ D) :
    A + C ≤ B + D := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      induction C using Quotient.inductionOn with | h c =>
        induction D using Quotient.inductionOn with | h d =>
          exact TensorRep.Restricts.ofTensor (hAB.blockSum hCD)

theorem mul_mono {A B C D : TensorClass} (hAB : A ≤ B) (hCD : C ≤ D) :
    A * C ≤ B * D := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      induction C using Quotient.inductionOn with | h c =>
        induction D using Quotient.inductionOn with | h d =>
          exact TensorRep.Restricts.ofTensor (hAB.product hCD)

theorem zero_le (A : TensorClass) : 0 ≤ A := by
  induction A using Quotient.inductionOn with | h a =>
    change 0 ≤ ofRep a
    rw [← ofTensor_coeff a]
    apply ofTensor_le
    refine ⟨fun x => x.elim, fun y => y.elim, fun z => z.elim, ?_⟩
    funext x
    exact x.elim

/-- Normalized additive multiplicative monotone quantities on actual tensor
classes. This definition asserts no existence theorem. -/
structure Character where
  toHom : TensorClass →+* ℝ≥0
  monotone' : Monotone toHom

noncomputable instance : CoeFun Character (fun _ => TensorClass → ℝ≥0) := ⟨fun f => f.toHom⟩

@[simp] theorem Character.map_zero (f : Character) : f 0 = 0 := f.toHom.map_zero
@[simp] theorem Character.map_one (f : Character) : f 1 = 1 := f.toHom.map_one
@[simp] theorem Character.map_add (f : Character) (A B : TensorClass) :
    f (A + B) = f A + f B := f.toHom.map_add A B
@[simp] theorem Character.map_mul (f : Character) (A B : TensorClass) :
    f (A * B) = f A * f B := f.toHom.map_mul A B

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass
