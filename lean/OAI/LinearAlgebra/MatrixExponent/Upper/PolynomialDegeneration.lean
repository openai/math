import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

open OAI.LinearAlgebra.MatrixExponent

noncomputable section

open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper

variable {X Y Z : Type*}

/-- The part of a tensor with total diagonal weight zero. -/
def weightedLimit (T : Tensor Coeff X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) : Tensor Coeff X Y Z :=
  fun x y z => if wx x + wy y + wz z = 0 then T x y z else 0

/-- The polynomial coefficient family. Negative total weights
occur only at zero coefficients in the degeneration theorem. -/
def weightedFamily (T : Tensor Coeff X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (t : Coeff) : Tensor Coeff X Y Z :=
  fun x y z => t ^ (wx x + wy y + wz z).toNat * T x y z

theorem weightedFamily_zero (T : Tensor Coeff X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z) :
    weightedFamily T wx wy wz 0 = weightedLimit T wx wy wz := by
  funext x y z
  by_cases hT : T x y z = 0
  · simp [weightedFamily, weightedLimit, hT]
  · have hnonneg := h x y z hT
    by_cases hw : wx x + wy y + wz z = 0
    · simp [weightedFamily, weightedLimit, hw]
    · have hnatne : (wx x + wy y + wz z).toNat ≠ 0 := by
        intro he
        have hc := Int.toNat_of_nonneg hnonneg
        rw [he] at hc
        exact hw hc.symm
      simp [weightedFamily, weightedLimit, hw, zero_pow hnatne]

/-- Diagonal local coefficient matrices multiply the three corresponding
coefficient factors, with all off-diagonal contributions vanishing. -/
theorem restrict_diagonal [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor Coeff X Y Z) (a : X → Coeff) (b : Y → Coeff) (c : Z → Coeff) :
    Tensor.restrict (fun x' x => if x = x' then a x else 0)
      (fun y' y => if y = y' then b y else 0)
      (fun z' z => if z = z' then c z else 0) T =
      fun x y z => a x * b y * c z * T x y z := by
  classical
  funext x y z
  simp [Tensor.restrict, ite_mul, mul_ite]

/-- At every nonzero parameter, the family is witnessed by actual
local substitutions: the diagonal entries are the respective integer powers. -/
theorem weightedFamily_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z)
    {t : Coeff} (ht : t ≠ 0) :
    weightedFamily T wx wy wz t ∈ LocalTensor.orbit T := by
  classical
  refine ⟨(fun x' x => if x = x' then t ^ wx x else 0),
    (fun y' y => if y = y' then t ^ wy y else 0),
    (fun z' z => if z = z' then t ^ wz z else 0), ?_⟩
  rw [restrict_diagonal]
  funext x y z
  by_cases hT : T x y z = 0
  · simp [weightedFamily, hT]
  · have hnonneg := h x y z hT
    dsimp [weightedFamily]
    rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg,
      zpow_add₀ ht, zpow_add₀ ht]

end OAI.LinearAlgebra.MatrixExponent.Upper
