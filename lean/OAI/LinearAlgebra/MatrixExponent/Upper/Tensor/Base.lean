import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
import Mathlib.Basic.NNReal.Defs

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# Concrete finite tensors and mutual restriction

Representatives use natural-number dimensions, so the quotient is a small type.
The relation is witnessed by the three actual local coefficient matrices. In
particular, no rank or restriction oracle occurs in this definition.
-/

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper

namespace CoefficientTensor

variable {X Y Z U V W X' Y' Z' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- `Restricts A B` means that the source `A` restricts to the target `B`. -/
def Restricts (A : Tensor Coeff X Y Z) (B : Tensor Coeff U V W) : Prop :=
  ∃ (a : U → X → Coeff) (b : V → Y → Coeff) (c : W → Z → Coeff),
    B = Tensor.restrict a b c A

theorem Restricts.refl (A : Tensor Coeff X Y Z) : Restricts A A := by
  classical
  exact ⟨_, _, _, (Tensor.restrict_identity A).symm⟩

theorem Restricts.trans [Fintype U] [Fintype V] [Fintype W]
    {A : Tensor Coeff X Y Z} {B : Tensor Coeff U V W} {C : Tensor Coeff X' Y' Z'}
    (hAB : Restricts A B) (hBC : Restricts B C) : Restricts A C := by
  rcases hAB with ⟨a, b, c, rfl⟩
  rcases hBC with ⟨d, e, f, rfl⟩
  exact ⟨Tensor.composeRestrictionMatrix d a, Tensor.composeRestrictionMatrix e b,
    Tensor.composeRestrictionMatrix f c, Tensor.restrict_restrict a b c d e f A⟩

theorem Restricts.pullback (A : Tensor Coeff X Y Z)
    (f : U → X) (g : V → Y) (h : W → Z) :
    Restricts A (Tensor.pullback f g h A) := by
  classical
  exact ⟨_, _, _, Tensor.pullback_eq_restrict f g h A⟩

theorem Restricts.rankAtMost {A : Tensor Coeff X Y Z} {B : Tensor Coeff U V W}
    {r : ℕ} (hAB : Restricts A B) (hA : Tensor.RankAtMost A r) :
    Tensor.RankAtMost B r := by
  rcases hAB with ⟨a, b, c, rfl⟩
  exact hA.restrict a b c

end CoefficientTensor

/-- A finite coefficient tensor with an explicit dimension on every leg. -/
structure TensorRep where
  xDim : ℕ
  yDim : ℕ
  zDim : ℕ
  coeff : Tensor Coeff (Fin xDim) (Fin yDim) (Fin zDim)

namespace TensorRep

/-- Encode arbitrary finite coordinates by their canonical finite enumeration. -/
noncomputable def ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) : TensorRep where
  xDim := Fintype.card X
  yDim := Fintype.card Y
  zDim := Fintype.card Z
  coeff := Tensor.pullback (Fintype.equivFin X).symm
    (Fintype.equivFin Y).symm (Fintype.equivFin Z).symm T

def Restricts (A B : TensorRep) : Prop := CoefficientTensor.Restricts A.coeff B.coeff

theorem Restricts.refl (A : TensorRep) : Restricts A A :=
  CoefficientTensor.Restricts.refl A.coeff

theorem Restricts.trans {A B C : TensorRep}
    (hAB : Restricts A B) (hBC : Restricts B C) : Restricts A C :=
  CoefficientTensor.Restricts.trans hAB hBC

theorem restricts_ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) :
    CoefficientTensor.Restricts T (ofTensor T).coeff :=
  CoefficientTensor.Restricts.pullback T _ _ _

theorem ofTensor_restricts {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) :
    CoefficientTensor.Restricts (ofTensor T).coeff T := by
  have h := CoefficientTensor.Restricts.pullback (ofTensor T).coeff
    (Fintype.equivFin X) (Fintype.equivFin Y) (Fintype.equivFin Z)
  have heq : Tensor.pullback (Fintype.equivFin X) (Fintype.equivFin Y)
      (Fintype.equivFin Z) (ofTensor T).coeff = T := by
    funext x y z
    simp only [ofTensor, Tensor.pullback, Equiv.symm_apply_apply]
  rcases h with ⟨a, b, c, hc⟩
  exact ⟨a, b, c, heq.symm.trans hc⟩

theorem Restricts.ofTensor {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor Coeff X Y Z} {U' : Tensor Coeff U V W}
    (h : CoefficientTensor.Restricts T U') : Restricts (ofTensor T) (ofTensor U') :=
  (ofTensor_restricts T).trans (h.trans (restricts_ofTensor U'))

/-- Mutual actual restriction, allowing unused or zero coordinates. -/
def Equivalent (A B : TensorRep) : Prop := Restricts A B ∧ Restricts B A

instance mutualRestriction : Setoid TensorRep where
  r := Equivalent
  iseqv := ⟨fun A => ⟨.refl A, .refl A⟩,
    fun h => ⟨h.2, h.1⟩,
    fun hAB hBC => ⟨hAB.1.trans hBC.1, hBC.2.trans hAB.2⟩⟩

theorem equivalent_ofTensor_coeff (A : TensorRep) : Equivalent (ofTensor A.coeff) A :=
  ⟨ofTensor_restricts A.coeff, restricts_ofTensor A.coeff⟩

end TensorRep

/-- The actual finite-tensor restriction quotient of the paper. -/
def TensorClass := Quotient TensorRep.mutualRestriction

namespace TensorClass

def ofRep (A : TensorRep) : TensorClass := Quotient.mk _ A

noncomputable def ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) : TensorClass := ofRep (TensorRep.ofTensor T)

theorem ofRep_eq {A B : TensorRep} (h : TensorRep.Equivalent A B) :
    ofRep A = ofRep B := Quotient.sound h

theorem ofTensor_coeff (A : TensorRep) : ofTensor A.coeff = ofRep A :=
  ofRep_eq (TensorRep.equivalent_ofTensor_coeff A)

theorem ofTensor_eq {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor Coeff X Y Z} {S : Tensor Coeff U V W}
    (hTS : CoefficientTensor.Restricts T S)
    (hST : CoefficientTensor.Restricts S T) : ofTensor T = ofTensor S :=
  ofRep_eq ⟨TensorRep.Restricts.ofTensor hTS, TensorRep.Restricts.ofTensor hST⟩

theorem ofTensor_pullback_equiv {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor Coeff X Y Z) (f : U ≃ X) (g : V ≃ Y) (h : W ≃ Z) :
    ofTensor (Tensor.pullback f g h T) = ofTensor T := by
  apply ofTensor_eq
  · have h' := CoefficientTensor.Restricts.pullback (Tensor.pullback f g h T)
      f.symm g.symm h.symm
    have heq : Tensor.pullback f.symm g.symm h.symm (Tensor.pullback f g h T) = T := by
      funext x y z
      simp only [Tensor.pullback, Equiv.apply_symm_apply]
    rw [heq] at h'
    exact h'
  · exact CoefficientTensor.Restricts.pullback T f g h

instance : LE TensorClass where
  le A B := Quotient.liftOn₂ A B (fun a b => TensorRep.Restricts b a) (by
    intro A B A' B' hA hB
    apply propext
    exact ⟨fun h => hB.2.trans (h.trans hA.1),
      fun h => hB.1.trans (h.trans hA.2)⟩)

instance : PartialOrder TensorClass where
  le := (· ≤ ·)
  le_refl := by
    intro A
    induction A using Quotient.inductionOn with | h a =>
      exact TensorRep.Restricts.refl a
  le_trans := by
    intro A B C
    induction A using Quotient.inductionOn with | h A =>
      induction B using Quotient.inductionOn with | h B =>
        induction C using Quotient.inductionOn with | h C =>
          exact fun hAB hBC => TensorRep.Restricts.trans hBC hAB
  le_antisymm := by
    intro A B
    induction A using Quotient.inductionOn with | h A =>
      induction B using Quotient.inductionOn with | h B =>
        exact fun hAB hBA => Quotient.sound ⟨hBA, hAB⟩

theorem ofTensor_le {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor Coeff X Y Z} {S : Tensor Coeff U V W}
    (h : CoefficientTensor.Restricts T S) : ofTensor S ≤ ofTensor T :=
  TensorRep.Restricts.ofTensor h

end TensorClass
end OAI.LinearAlgebra.MatrixExponent.Upper
