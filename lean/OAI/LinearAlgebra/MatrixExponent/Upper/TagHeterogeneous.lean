import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Separation
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.Base
import OAI.LinearAlgebra.MatrixExponent.Upper.PolynomialSectors
import Mathlib.Tactic.FinCases

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

/-!
# Heterogeneous shared-first-leg tensors

Padding a branch adds only zero coordinates. The extra uniform labels used by
the separation construction are removed by actual independent local maps.
The first leg is shared throughout; no direct-sum additivity is used here.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.TagHeterogeneous

variable {X Y Z Y₀ Z₀ Y₁ Z₁ Y₂ Z₂ : Type*}

/-- Two heterogeneous branches with one common first coordinate. -/
def sharedTwo (T : Tensor Coeff X Y₀ Z₀) (S : Tensor Coeff X Y₁ Z₁) :
    Tensor Coeff X (Y₀ ⊕ Y₁) (Z₀ ⊕ Z₁)
  | x, .inl y, .inl z => T x y z
  | x, .inr y, .inr z => S x y z
  | _, _, _ => 0

/-- Zero extension into the left summand on the last two legs. -/
def padLeft (T : Tensor Coeff X Y₀ Z₀) : Tensor Coeff X (Y₀ ⊕ Y₁) (Z₀ ⊕ Z₁)
  | x, .inl y, .inl z => T x y z
  | _, _, _ => 0

/-- Zero extension into the right summand on the last two legs. -/
def padRight (T : Tensor Coeff X Y₁ Z₁) : Tensor Coeff X (Y₀ ⊕ Y₁) (Z₀ ⊕ Z₁)
  | x, .inr y, .inr z => T x y z
  | _, _, _ => 0

section Padding

variable [Fintype X] [Fintype Y₀] [Fintype Z₀]
variable [Fintype Y₁] [Fintype Z₁]

/-- Zero padding is an equivalence under mutual actual restriction. -/
theorem ofTensor_padLeft (T : Tensor Coeff X Y₀ Z₀) :
    TensorClass.ofTensor (padLeft (Y₁ := Y₁) (Z₁ := Z₁) T) =
      TensorClass.ofTensor T := by
  classical
  apply TensorClass.ofTensor_eq
  · have h := CoefficientTensor.Restricts.pullback
      (padLeft (Y₁ := Y₁) (Z₁ := Z₁) T) id Sum.inl Sum.inl
    exact h
  · refine ⟨(fun x i => if i = x then 1 else 0),
      (fun y j => match y with
        | .inl v => if j = v then 1 else 0
        | .inr _ => 0),
      (fun z k => match z with
        | .inl v => if k = v then 1 else 0
        | .inr _ => 0), ?_⟩
    funext x y z
    cases y <;> cases z <;>
      simp [padLeft, Tensor.restrict, ite_mul, mul_ite]

/-- Right zero padding also has explicit inclusion and projection maps. -/
theorem ofTensor_padRight (T : Tensor Coeff X Y₁ Z₁) :
    TensorClass.ofTensor (padRight (Y₀ := Y₀) (Z₀ := Z₀) T) =
      TensorClass.ofTensor T := by
  classical
  apply TensorClass.ofTensor_eq
  · have h := CoefficientTensor.Restricts.pullback
      (padRight (Y₀ := Y₀) (Z₀ := Z₀) T) id Sum.inr Sum.inr
    exact h
  · refine ⟨(fun x i => if i = x then 1 else 0),
      (fun y j => match y with
        | .inl _ => 0
        | .inr v => if j = v then 1 else 0),
      (fun z k => match z with
        | .inl _ => 0
        | .inr v => if k = v then 1 else 0), ?_⟩
    funext x y z
    cases y <;> cases z <;>
      simp [padRight, Tensor.restrict, ite_mul, mul_ite]

end Padding

/-- Keep just one matched pair of sectors in a common ambient tensor. -/
def maskedFamily {M : ℕ} (ly : Y → Fin M) (lz : Z → Fin M)
    (T : Tensor Coeff X Y Z) (h : Fin M) : Tensor Coeff X Y Z :=
  fun x y z => if ly y = h ∧ lz z = h then T x y z else 0

section Labels

variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Redundant labels are removed by selecting each coordinate's own sector;
the reverse maps are the corresponding zero extensions. -/
theorem ofTensor_shared_maskedFamily {M : ℕ}
    (ly : Y → Fin M) (lz : Z → Fin M) (T : Tensor Coeff X Y Z)
    (hcross : ∀ x y z, ly y ≠ lz z → T x y z = 0) :
    TensorClass.ofTensor (Separation.shared (maskedFamily ly lz T)) =
      TensorClass.ofTensor T := by
  classical
  apply TensorClass.ofTensor_eq
  · have hp : Tensor.pullback id (fun y => (ly y, y)) (fun z => (lz z, z))
        (Separation.shared (maskedFamily ly lz T)) = T := by
      funext x y z
      by_cases h : ly y = lz z
      · simp [Tensor.pullback, Separation.shared, maskedFamily, h]
      · simp [Tensor.pullback, Separation.shared, h, hcross x y z h]
    simpa only [hp] using
      (CoefficientTensor.Restricts.pullback (Separation.shared (maskedFamily ly lz T))
        id (fun y => (ly y, y)) (fun z => (lz z, z)))
  · refine ⟨(fun x i => if i = x then 1 else 0),
      (fun y j => if j = y.2 then if ly y.2 = y.1 then 1 else 0 else 0),
      (fun z k => if k = z.2 then if lz z.2 = z.1 then 1 else 0 else 0), ?_⟩
    funext x y z
    by_cases h : y.1 = z.1
    · simp [Tensor.restrict, Separation.shared, maskedFamily, h,
        ite_mul, mul_ite]
      split_ifs <;> simp_all
    · by_cases hy : ly y.2 = y.1
      · by_cases hz : lz z.2 = z.1
        · have hc : T x y.2 z.2 = 0 := hcross _ _ _ (by simpa [hy, hz] using h)
          simp [Tensor.restrict, Separation.shared, h, hy, hz,
            hc, ite_mul, mul_ite]
        · simp [Tensor.restrict, Separation.shared, h, hy, hz,
            mul_ite]
      · simp [Tensor.restrict, Separation.shared, h, hy,
          mul_ite]

end Labels

/-- A two-sector label independent of the coordinate inside the sector. -/
def twoLabel : Y₀ ⊕ Y₁ → Fin 2
  | .inl _ => 0
  | .inr _ => 1

/-- Both branches now use the same ambient last two legs. -/
def twoFamily (T : Tensor Coeff X Y₀ Z₀) (S : Tensor Coeff X Y₁ Z₁) :
    Fin 2 → Tensor Coeff X (Y₀ ⊕ Y₁) (Z₀ ⊕ Z₁) :=
  ![padLeft T, padRight S]

theorem twoFamily_eq_maskedFamily
    (T : Tensor Coeff X Y₀ Z₀) (S : Tensor Coeff X Y₁ Z₁) :
    twoFamily T S = maskedFamily twoLabel twoLabel (sharedTwo T S) := by
  funext h x y z
  fin_cases h <;> cases y <;> cases z <;>
    simp [twoFamily, maskedFamily, twoLabel, sharedTwo, padLeft, padRight]

theorem ofTensor_shared_twoFamily
    [Fintype X] [Fintype Y₀] [Fintype Z₀] [Fintype Y₁] [Fintype Z₁]
    (T : Tensor Coeff X Y₀ Z₀) (S : Tensor Coeff X Y₁ Z₁) :
    TensorClass.ofTensor (Separation.shared (twoFamily T S)) =
      TensorClass.ofTensor (sharedTwo T S) := by
  rw [twoFamily_eq_maskedFamily]
  apply ofTensor_shared_maskedFamily
  intro x y z h
  cases y <;> cases z <;> simp_all [sharedTwo, twoLabel]

theorem ofTensor_twoFamily
    [Fintype X] [Fintype Y₀] [Fintype Z₀] [Fintype Y₁] [Fintype Z₁]
    (T : Tensor Coeff X Y₀ Z₀) (S : Tensor Coeff X Y₁ Z₁) (h : Fin 2) :
    TensorClass.ofTensor (twoFamily T S h) =
      ![TensorClass.ofTensor T, TensorClass.ofTensor S] h := by
  fin_cases h <;> simp [twoFamily, ofTensor_padLeft, ofTensor_padRight]

/-- Three heterogeneous branches, still sharing one first leg. -/
def sharedThree (T : Tensor Coeff X Y₀ Z₀) (S : Tensor Coeff X Y₁ Z₁)
    (U : Tensor Coeff X Y₂ Z₂) :
    Tensor Coeff X (Y₀ ⊕ (Y₁ ⊕ Y₂)) (Z₀ ⊕ (Z₁ ⊕ Z₂)) :=
  sharedTwo T (sharedTwo S U)

def threeLabel : Y₀ ⊕ (Y₁ ⊕ Y₂) → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

/-- The three padded branches used by the uniform tag theorem. -/
def threeFamily (T : Tensor Coeff X Y₀ Z₀) (S : Tensor Coeff X Y₁ Z₁)
    (U : Tensor Coeff X Y₂ Z₂) :
    Fin 3 → Tensor Coeff X (Y₀ ⊕ (Y₁ ⊕ Y₂)) (Z₀ ⊕ (Z₁ ⊕ Z₂)) :=
  ![padLeft T, padRight (padLeft S), padRight (padRight U)]

theorem threeFamily_eq_maskedFamily
    (T : Tensor Coeff X Y₀ Z₀) (S : Tensor Coeff X Y₁ Z₁)
    (U : Tensor Coeff X Y₂ Z₂) :
    threeFamily T S U = maskedFamily threeLabel threeLabel (sharedThree T S U) := by
  funext h x y z
  fin_cases h <;> rcases y with y | (y | y) <;> rcases z with z | (z | z) <;>
    simp [threeFamily, maskedFamily, threeLabel, sharedThree, sharedTwo, padLeft, padRight]

theorem ofTensor_shared_threeFamily
    [Fintype X] [Fintype Y₀] [Fintype Z₀] [Fintype Y₁] [Fintype Z₁]
    [Fintype Y₂] [Fintype Z₂]
    (T : Tensor Coeff X Y₀ Z₀) (S : Tensor Coeff X Y₁ Z₁)
    (U : Tensor Coeff X Y₂ Z₂) :
    TensorClass.ofTensor (Separation.shared (threeFamily T S U)) =
      TensorClass.ofTensor (sharedThree T S U) := by
  rw [threeFamily_eq_maskedFamily]
  apply ofTensor_shared_maskedFamily
  intro x y z h
  rcases y with y | (y | y) <;> rcases z with z | (z | z) <;>
    simp_all [sharedThree, sharedTwo, threeLabel]

theorem ofTensor_threeFamily
    [Fintype X] [Fintype Y₀] [Fintype Z₀] [Fintype Y₁] [Fintype Z₁]
    [Fintype Y₂] [Fintype Z₂]
    (T : Tensor Coeff X Y₀ Z₀) (S : Tensor Coeff X Y₁ Z₁)
    (U : Tensor Coeff X Y₂ Z₂) (h : Fin 3) :
    TensorClass.ofTensor (threeFamily T S U h) =
      ![TensorClass.ofTensor T, TensorClass.ofTensor S, TensorClass.ofTensor U] h := by
  fin_cases h <;> simp [threeFamily, ofTensor_padLeft, ofTensor_padRight]

/-- The middle polynomial branch keeps its original first-leg reversal. -/
def triplingMiddleTensor (a h : ℕ) :
    Tensor Coeff (Fin a) (Fin (a + h - 1)) (Fin h) :=
  fun x k j => polynomialTensor a h (triplingReverse x) j k

/-- The actual polynomial sector assembly is exactly a heterogeneous shared
tensor; in particular all six mismatched sector blocks remain zero. -/
theorem triplingSectorTensor_eq_sharedThree (a h : ℕ) :
    triplingSectorTensor a h = sharedThree (polynomialTensor a h)
      (triplingMiddleTensor a h) (polynomialTensor a h) := by
  funext x y z
  rcases y with y | (y | y) <;> rcases z with z | (z | z) <;> rfl

/-- This is the exact uniform-tag input representing the three-sector
polynomial degeneration, with a literal common first-input space. -/
theorem ofTensor_tripling_uniform (a h : ℕ) :
    TensorClass.ofTensor (Separation.shared
      (threeFamily (polynomialTensor a h) (triplingMiddleTensor a h)
        (polynomialTensor a h))) = TensorClass.ofTensor (triplingSectorTensor a h) := by
  rw [ofTensor_shared_threeFamily, triplingSectorTensor_eq_sharedThree]

end OAI.LinearAlgebra.MatrixExponent.Upper.TagHeterogeneous
