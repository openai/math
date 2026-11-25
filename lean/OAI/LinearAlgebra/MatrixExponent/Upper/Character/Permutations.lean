import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.Semiring
import OAI.LinearAlgebra.MatrixExponent.Upper.PolynomialTensor
import OAI.LinearAlgebra.MatrixExponent.Upper.Character.Dots
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic.FinCases

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

/-!
# Permuting the three actual tensor legs

The two adjacent swaps act on coefficient arrays and on their actual local
restriction witnesses. Their quotient actions preserve the semiring operations.
The six induced characters therefore remain normalized restriction-monotone
characters; their six values form a multiset invariant under either swap.
-/

noncomputable section

open scoped BigOperators NNReal
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper
namespace CoefficientTensor

variable {X Y Z U V W : Type*}

def swapXY (T : Tensor Coeff X Y Z) : Tensor Coeff Y X Z := fun y x z => T x y z
def swapYZ (T : Tensor Coeff X Y Z) : Tensor Coeff X Z Y := fun x z y => T x y z

theorem Restricts.swapXY [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor Coeff X Y Z} {S : Tensor Coeff U V W} (h : Restricts T S) :
    Restricts (swapXY T) (swapXY S) := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨b, a, c, ?_⟩
  funext y x z
  simp only [CoefficientTensor.swapXY, Tensor.restrict]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem Restricts.swapYZ [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor Coeff X Y Z} {S : Tensor Coeff U V W} (h : Restricts T S) :
    Restricts (swapYZ T) (swapYZ S) := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨a, c, b, ?_⟩
  funext x z y
  simp only [CoefficientTensor.swapYZ, Tensor.restrict]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem swapXY_blockSum (T : Tensor Coeff X Y Z) (S : Tensor Coeff U V W) :
    swapXY (blockSum T S) = blockSum (swapXY T) (swapXY S) := by
  funext x y z
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;> rfl

theorem swapYZ_blockSum (T : Tensor Coeff X Y Z) (S : Tensor Coeff U V W) :
    swapYZ (blockSum T S) = blockSum (swapYZ T) (swapYZ S) := by
  funext x y z
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;> rfl

theorem swapXY_product (T : Tensor Coeff X Y Z) (S : Tensor Coeff U V W) :
    swapXY (Tensor.product T S) = Tensor.product (swapXY T) (swapXY S) := rfl

theorem swapYZ_product (T : Tensor Coeff X Y Z) (S : Tensor Coeff U V W) :
    swapYZ (Tensor.product T S) = Tensor.product (swapYZ T) (swapYZ S) := rfl

end CoefficientTensor

namespace TensorRep

def swapXY (T : TensorRep) : TensorRep where
  xDim := T.yDim
  yDim := T.xDim
  zDim := T.zDim
  coeff := CoefficientTensor.swapXY T.coeff

def swapYZ (T : TensorRep) : TensorRep where
  xDim := T.xDim
  yDim := T.zDim
  zDim := T.yDim
  coeff := CoefficientTensor.swapYZ T.coeff

theorem Restricts.swapXY {T S : TensorRep} (h : Restricts T S) :
    Restricts (swapXY T) (swapXY S) := CoefficientTensor.Restricts.swapXY h

theorem Restricts.swapYZ {T S : TensorRep} (h : Restricts T S) :
    Restricts (swapYZ T) (swapYZ S) := CoefficientTensor.Restricts.swapYZ h

end TensorRep

namespace TensorClass

def swapXY : TensorClass → TensorClass :=
  Quotient.map TensorRep.swapXY (fun _ _ h => ⟨h.1.swapXY, h.2.swapXY⟩)

def swapYZ : TensorClass → TensorClass :=
  Quotient.map TensorRep.swapYZ (fun _ _ h => ⟨h.1.swapYZ, h.2.swapYZ⟩)

@[simp] theorem swapXY_ofTensor {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor Coeff X Y Z) :
    swapXY (ofTensor T) = ofTensor (CoefficientTensor.swapXY T) := rfl

@[simp] theorem swapYZ_ofTensor {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor Coeff X Y Z) :
    swapYZ (ofTensor T) = ofTensor (CoefficientTensor.swapYZ T) := rfl

@[simp] theorem swapXY_swapXY (T : TensorClass) : swapXY (swapXY T) = T := by
  induction T using Quotient.inductionOn with | h T => rfl

@[simp] theorem swapYZ_swapYZ (T : TensorClass) : swapYZ (swapYZ T) = T := by
  induction T using Quotient.inductionOn with | h T => rfl

theorem swap_braid (T : TensorClass) :
    swapXY (swapYZ (swapXY T)) = swapYZ (swapXY (swapYZ T)) := by
  induction T using Quotient.inductionOn with | h T => rfl

theorem swapXY_mono : Monotone swapXY := by
  intro A B h
  induction A using Quotient.inductionOn with | h A =>
    induction B using Quotient.inductionOn with | h B =>
      exact TensorRep.Restricts.swapXY h

theorem swapYZ_mono : Monotone swapYZ := by
  intro A B h
  induction A using Quotient.inductionOn with | h A =>
    induction B using Quotient.inductionOn with | h B =>
      exact TensorRep.Restricts.swapYZ h

@[simp] theorem swapXY_zero : swapXY (0 : TensorClass) = 0 := by
  change swapXY (ofTensor emptyTensor) = ofTensor emptyTensor
  rw [swapXY_ofTensor]
  congr 1
  funext x
  exact x.elim

@[simp] theorem swapYZ_zero : swapYZ (0 : TensorClass) = 0 := by
  change swapYZ (ofTensor emptyTensor) = ofTensor emptyTensor
  rw [swapYZ_ofTensor]
  congr 1
  funext x
  exact x.elim

@[simp] theorem swapXY_one : swapXY (1 : TensorClass) = 1 := rfl
@[simp] theorem swapYZ_one : swapYZ (1 : TensorClass) = 1 := rfl

@[simp] theorem swapXY_add (A B : TensorClass) : swapXY (A + B) = swapXY A + swapXY B := by
  induction A using Quotient.inductionOn with | h A =>
    induction B using Quotient.inductionOn with | h B =>
      change swapXY (ofRep A + ofRep B) = swapXY (ofRep A) + swapXY (ofRep B)
      rw [← ofTensor_coeff A, ← ofTensor_coeff B]
      simp only [ofTensor_add, swapXY_ofTensor, CoefficientTensor.swapXY_blockSum]

@[simp] theorem swapYZ_add (A B : TensorClass) : swapYZ (A + B) = swapYZ A + swapYZ B := by
  induction A using Quotient.inductionOn with | h A =>
    induction B using Quotient.inductionOn with | h B =>
      change swapYZ (ofRep A + ofRep B) = swapYZ (ofRep A) + swapYZ (ofRep B)
      rw [← ofTensor_coeff A, ← ofTensor_coeff B]
      simp only [ofTensor_add, swapYZ_ofTensor, CoefficientTensor.swapYZ_blockSum]

@[simp] theorem swapXY_mul (A B : TensorClass) : swapXY (A * B) = swapXY A * swapXY B := by
  induction A using Quotient.inductionOn with | h A =>
    induction B using Quotient.inductionOn with | h B =>
      change swapXY (ofRep A * ofRep B) = swapXY (ofRep A) * swapXY (ofRep B)
      rw [← ofTensor_coeff A, ← ofTensor_coeff B]
      simp only [ofTensor_mul, swapXY_ofTensor, CoefficientTensor.swapXY_product]

@[simp] theorem swapYZ_mul (A B : TensorClass) : swapYZ (A * B) = swapYZ A * swapYZ B := by
  induction A using Quotient.inductionOn with | h A =>
    induction B using Quotient.inductionOn with | h B =>
      change swapYZ (ofRep A * ofRep B) = swapYZ (ofRep A) * swapYZ (ofRep B)
      rw [← ofTensor_coeff A, ← ofTensor_coeff B]
      simp only [ofTensor_mul, swapYZ_ofTensor, CoefficientTensor.swapYZ_product]

def swapXYHom : TensorClass →+* TensorClass where
  toFun := swapXY
  map_zero' := swapXY_zero
  map_one' := swapXY_one
  map_add' := swapXY_add
  map_mul' := swapXY_mul

def swapYZHom : TensorClass →+* TensorClass where
  toFun := swapYZ
  map_zero' := swapYZ_zero
  map_one' := swapYZ_one
  map_add' := swapYZ_add
  map_mul' := swapYZ_mul

/-- All six permutations, in the order `id, XY, YZ, XY·YZ, YZ·XY, XY·YZ·XY`. -/
def permuteHom : Fin 6 → TensorClass →+* TensorClass :=
  ![RingHom.id _, swapXYHom, swapYZHom, swapXYHom.comp swapYZHom,
    swapYZHom.comp swapXYHom, swapXYHom.comp (swapYZHom.comp swapXYHom)]

def permute (i : Fin 6) (T : TensorClass) : TensorClass := permuteHom i T

theorem permute_mono (i : Fin 6) : Monotone (permute i) := by
  fin_cases i
  · exact monotone_id
  · exact swapXY_mono
  · exact swapYZ_mono
  · exact swapXY_mono.comp swapYZ_mono
  · exact swapYZ_mono.comp swapXY_mono
  · exact swapXY_mono.comp (swapYZ_mono.comp swapXY_mono)

/-- Composing an actual tensor character with any of the six leg permutations
again gives a normalized monotone semiring character. -/
def Character.permuted (f : Character) (i : Fin 6) : Character where
  toHom := f.toHom.comp (permuteHom i)
  monotone' := f.monotone'.comp (permute_mono i)

@[simp] theorem Character.permuted_apply (f : Character) (i : Fin 6) (T : TensorClass) :
    f.permuted i T = f (permute i T) := rfl

/-- Right multiplication of the six leg permutations by the first swap. -/
def permuteSwapXY : Fin 6 ≃ Fin 6 where
  toFun := ![1, 0, 4, 5, 2, 3]
  invFun := ![1, 0, 4, 5, 2, 3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Right multiplication of the six leg permutations by the second swap. -/
def permuteSwapYZ : Fin 6 ≃ Fin 6 where
  toFun := ![2, 3, 0, 1, 5, 4]
  invFun := ![2, 3, 0, 1, 5, 4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem permute_swapXY (i : Fin 6) (T : TensorClass) :
    permute i (swapXY T) = permute (permuteSwapXY i) T := by
  fin_cases i <;>
    simp [permute, permuteHom, permuteSwapXY, swapXYHom, swapYZHom]

theorem permute_swapYZ (i : Fin 6) (T : TensorClass) :
    permute i (swapYZ T) = permute (permuteSwapYZ i) T := by
  fin_cases i <;>
    simp [permute, permuteHom, permuteSwapYZ, swapXYHom, swapYZHom, swap_braid]

theorem Character.permuted_swapXY (f : Character) (i : Fin 6) (T : TensorClass) :
    f.permuted i (swapXY T) = f.permuted (permuteSwapXY i) T := by
  simp only [Character.permuted_apply, permute_swapXY]

theorem Character.permuted_swapYZ (f : Character) (i : Fin 6) (T : TensorClass) :
    f.permuted i (swapYZ T) = f.permuted (permuteSwapYZ i) T := by
  simp only [Character.permuted_apply, permute_swapYZ]

/-- Multiplicities are retained even when different permutations have equal
character values. -/
def Character.sixValues (f : Character) (T : TensorClass) : Multiset ℝ≥0 :=
  {f T} + {f (swapXY T)} + {f (swapYZ T)} +
    {f (swapXY (swapYZ T))} + {f (swapYZ (swapXY T))} +
    {f (swapXY (swapYZ (swapXY T)))}

theorem Character.sixValues_swapXY (f : Character) (T : TensorClass) :
    f.sixValues (swapXY T) = f.sixValues T := by
  simp only [Character.sixValues, swapXY_swapXY]
  ac_rfl

theorem Character.sixValues_swapYZ (f : Character) (T : TensorClass) :
    f.sixValues (swapYZ T) = f.sixValues T := by
  have hfour : swapXY (swapYZ (swapXY (swapYZ T))) = swapYZ (swapXY T) := by
    rw [swap_braid, swapYZ_swapYZ]
  rw [Character.sixValues, hfour]
  simp only [Character.sixValues, swapYZ_swapYZ, ← swap_braid]
  ac_rfl

/-- Swapping the two polynomial inputs is a literal coefficient reindexing. -/
theorem swapXY_polynomialTensor (a b : ℕ) :
    swapXY (ofTensor (polynomialTensor a b)) = ofTensor (polynomialTensor b a) := by
  rw [swapXY_ofTensor]
  let e : Fin (a + b - 1) ≃ Fin (b + a - 1) := finCongr (by omega)
  have h : CoefficientTensor.swapXY (polynomialTensor a b) =
      Tensor.pullback (Equiv.refl _) (Equiv.refl _) e (polynomialTensor b a) := by
    funext j i k
    simp [CoefficientTensor.swapXY, Tensor.pullback, polynomialTensor, e, Nat.add_comm]
  rw [h]
  exact ofTensor_pullback_equiv _ _ _ _

theorem Character.sixValues_polynomialTensor_swap (f : Character) (a b : ℕ) :
    f.sixValues (ofTensor (polynomialTensor a b)) =
      f.sixValues (ofTensor (polynomialTensor b a)) := by
  rw [← swapXY_polynomialTensor a b, f.sixValues_swapXY]

@[simp] theorem swapXY_dotX (n : ℕ) : swapXY (dotX n) = dotY n := by
  rw [dotX, swapXY_ofTensor]
  rfl

@[simp] theorem swapXY_dotY (n : ℕ) : swapXY (dotY n) = dotX n := by
  rw [← swapXY_dotX, swapXY_swapXY]

@[simp] theorem swapXY_dotZ (n : ℕ) : swapXY (dotZ n) = dotZ n := by
  rw [dotZ, swapXY_ofTensor]
  congr 1
  funext x y z
  simp [CoefficientTensor.swapXY, CoefficientTensor.dotZCoeff, eq_comm]

@[simp] theorem swapYZ_dotX (n : ℕ) : swapYZ (dotX n) = dotX n := by
  rw [dotX, swapYZ_ofTensor]
  congr 1
  funext x y z
  simp [CoefficientTensor.swapYZ, CoefficientTensor.dotXCoeff, eq_comm]

@[simp] theorem swapYZ_dotY (n : ℕ) : swapYZ (dotY n) = dotZ n := by
  rw [dotY, swapYZ_ofTensor]
  rfl

@[simp] theorem swapYZ_dotZ (n : ℕ) : swapYZ (dotZ n) = dotY n := by
  rw [← swapYZ_dotY, swapYZ_swapYZ]

@[simp] theorem swapXY_square (n : ℕ) : swapXY (square n) = square n := by
  rw [← dotX_mul_dotY_mul_dotZ]
  simp only [swapXY_mul, swapXY_dotX, swapXY_dotY, swapXY_dotZ]
  ac_rfl

@[simp] theorem swapYZ_square (n : ℕ) : swapYZ (square n) = square n := by
  rw [← dotX_mul_dotY_mul_dotZ]
  simp only [swapYZ_mul, swapYZ_dotX, swapYZ_dotY, swapYZ_dotZ]
  ac_rfl

@[simp] theorem permute_square (i : Fin 6) (n : ℕ) : permute i (square n) = square n := by
  fin_cases i <;>
    simp [permute, permuteHom, swapXYHom, swapYZHom]

@[simp] theorem Character.permuted_square (f : Character) (i : Fin 6) (n : ℕ) :
    f.permuted i (square n) = f (square n) := by
  rw [Character.permuted_apply, permute_square]

/-- Each of the three singleton-leg orientations occurs exactly twice among
the first-leg pairings evaluated by the six permuted characters. -/
theorem Character.permuted_dotX (f : Character) (i : Fin 6) (n : ℕ) :
    f.permuted i (dotX n) = ![f (dotX n), f (dotY n), f (dotX n),
      f (dotY n), f (dotZ n), f (dotZ n)] i := by
  fin_cases i <;>
    simp [Character.permuted_apply, permute, permuteHom, swapXYHom, swapYZHom]

theorem Character.sixValues_dotX (f : Character) (n : ℕ) :
    f.sixValues (dotX n) =
      ({f (dotX n)} + {f (dotY n)} + {f (dotZ n)}) +
      ({f (dotX n)} + {f (dotY n)} + {f (dotZ n)}) := by
  simp only [Character.sixValues, swapXY_dotX, swapYZ_dotX, swapYZ_dotY, swapXY_dotZ]
  ac_rfl

end TensorClass
end OAI.LinearAlgebra.MatrixExponent.Upper
