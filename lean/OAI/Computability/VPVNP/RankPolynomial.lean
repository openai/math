import OAI.Computability.VPVNP.ShiftedPairing
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The determinant used for rank queries

Appendix D.2 of *VP and VNP differ over every field* forms a weighted Gram matrix
over a polynomial ring. The coefficient of degree `q` in its reverse characteristic
polynomial is a signed sum of squares of minors of the original rectangular matrix.
Each square is tagged by the sum of its one-based row and column indices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

open Polynomial Set VPVNP.Crossing
open scoped Matrix

variable {K : Type*} [CommRing K] {n m q : ℕ}

/-- Sum of the one-based indices selected for a minor. -/
def indexWeight (I : powersetCard (Fin n) q) : ℕ :=
  ∑ i ∈ I.val, (i.val + 1)

theorem indexWeight_eq_sum (I : powersetCard (Fin n) q) :
    indexWeight I = ∑ i : Fin q, ((powersetCard.ofFinEmbEquiv.symm I i).val + 1) := by
  rw [indexWeight, ← Finset.sum_coe_sort]
  exact ((powersetCard.orderIsoOfFin I).toEquiv.sum_comp fun i => i.val.val + 1).symm

/-- The diagonal tagging the one-based index of each row or column. -/
noncomputable def weightDiagonal (K : Type*) [CommRing K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (Polynomial K) :=
  Matrix.diagonal fun i => X ^ (i.val + 1)

/-- The matrix `D₁(z) M D₂(z) Mᵀ`, with constant entries of `M` embedded by `C`. -/
noncomputable def weightedGram (M : Matrix (Fin n) (Fin m) K) :
    Matrix (Fin n) (Fin n) (Polynomial K) :=
  weightDiagonal K n * M.map C * weightDiagonal K m * (M.map C)ᵀ

/-- The determinant `det(1 - u G(z))` as a polynomial in `u` with coefficients in `K[z]`. -/
noncomputable def rankPolynomial (M : Matrix (Fin n) (Fin m) K) :
    Polynomial (Polynomial K) :=
  (weightedGram M).charpolyRev

private theorem scaled_minor (M : Matrix (Fin n) (Fin m) K)
    (I : powersetCard (Fin n) q) (J : powersetCard (Fin m) q) :
    compound q (weightDiagonal K n * M.map C * weightDiagonal K m) I J =
      X ^ (indexWeight I + indexWeight J) * C (compound q M I J) := by
  let r := powersetCard.ofFinEmbEquiv.symm I
  let c := powersetCard.ofFinEmbEquiv.symm J
  let A := M.submatrix r c
  have restrictWeights :
      (weightDiagonal K n * M.map C * weightDiagonal K m).submatrix r c =
        Matrix.diagonal (fun i : Fin q => X ^ ((r i).val + 1)) *
          C.mapMatrix A * Matrix.diagonal (fun j : Fin q => X ^ ((c j).val + 1)) := by
    ext i j
    simp [weightDiagonal, A]
  change ((weightDiagonal K n * M.map C * weightDiagonal K m).submatrix r c).det =
    X ^ (indexWeight I + indexWeight J) * C A.det
  rw [restrictWeights, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_diagonal, ← C.map_det, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
    indexWeight_eq_sum I, indexWeight_eq_sum J, pow_add]
  ac_rfl

/-- Cauchy–Binet expands each principal minor of the weighted Gram matrix. -/
theorem weightedGram_minor (M : Matrix (Fin n) (Fin m) K) (I : powersetCard (Fin n) q) :
    compound q (weightedGram M) I I =
      ∑ J : powersetCard (Fin m) q,
        X ^ (indexWeight I + indexWeight J) * C (compound q M I J) ^ 2 := by
  rw [weightedGram, compound_mul, Matrix.mul_apply, compound_transpose]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [scaled_minor, Matrix.transpose_apply, pow_two, mul_assoc]
  have hmap : compound q (M.map C) I J = C (compound q M I J) :=
    (C.map_det (M.submatrix (powersetCard.ofFinEmbEquiv.symm I)
      (powersetCard.ofFinEmbEquiv.symm J))).symm
  rw [hmap]

/-- Each reverse characteristic coefficient is the signed trace of the corresponding
compound matrix, also when the requested minor size exceeds the dimension. -/
theorem charpolyRev_coeff_eq_sum_compound {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (q : ℕ) :
    A.charpolyRev.coeff q =
      (-1) ^ q * ∑ I : Set.powersetCard (Fin n) q, compound q A I I := by
  classical
  have hrev : A.charpolyRev = (1 + (X : R[X]) • (-A).map C).det := by
    simp only [Matrix.charpolyRev, sub_eq_add_neg]
    congr 2
    rw [Matrix.map_neg C (map_neg C) A, smul_neg]
  rw [hrev, Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  simp only [Matrix.submatrix_neg, Pi.neg_apply, Matrix.det_neg, Fintype.card_coe, Finset.mul_sum]
  rw [Finset.sum_subtype _ (fun _ => Finset.mem_powersetCard_univ) _]
  apply Finset.sum_congr rfl
  intro I _
  rw [I.property]
  congr 1
  exact (Matrix.det_submatrix_equiv_self (Set.powersetCard.orderIsoOfFin I).toEquiv
    (A.submatrix Subtype.val Subtype.val)).symm

/-- The coefficient identity of Appendix D.2 over the coefficient ring, in every
characteristic. For `q` larger than a matrix dimension the sum of minors is empty. -/
theorem rankPolynomial_coeff (M : Matrix (Fin n) (Fin m) K) (q : ℕ) :
    (rankPolynomial M).coeff q = (-1) ^ q * ∑ I : powersetCard (Fin n) q,
      ∑ J : powersetCard (Fin m) q,
        X ^ (indexWeight I + indexWeight J) * C (compound q M I J) ^ 2 := by
  rw [rankPolynomial, charpolyRev_coeff_eq_sum_compound]
  simp_rw [weightedGram_minor]

end RankQuery

end VPVNP
end Computability
end OAI
