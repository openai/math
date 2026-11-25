import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.Blocks
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.Rank
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

/-!
# First-leg coefficient flattening

The invariant is the matrix rank of the actual coefficient array, with the
second and third coordinates paired into its rows. Local tensor restrictions
act by matrix multiplication on both sides. This invariant, unlike ordinary
tensor rank, is additive on full heterogeneous direct sums.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper
namespace CoefficientTensor

variable {X Y Z U V W : Type*}

/-- Pair the last two legs; the first leg indexes matrix columns. -/
def firstFlattening (T : Tensor Coeff X Y Z) : Matrix (Y × Z) X Coeff :=
  fun yz x => T x yz.1 yz.2

/-- The finite dimension of the space spanned by the first-leg slices. -/
def flatteningRank [Fintype X] (T : Tensor Coeff X Y Z) : ℕ :=
  (firstFlattening T).rank

theorem firstFlattening_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (a : U → X → Coeff) (b : V → Y → Coeff) (c : W → Z → Coeff)
    (T : Tensor Coeff X Y Z) :
    firstFlattening (Tensor.restrict a b c T) =
      (show Matrix (V × W) (Y × Z) Coeff from
        fun vw yz => b vw.1 yz.1 * c vw.2 yz.2) * firstFlattening T *
        Matrix.transpose a := by
  funext vw u
  change (∑ x, ∑ y, ∑ z, a u x * b vw.1 y * c vw.2 z * T x y z) =
    ∑ x, (∑ yz : Y × Z, (b vw.1 yz.1 * c vw.2 yz.2) * T x yz.1 yz.2) * a u x
  simp only [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem flatteningRank_mono [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor Coeff X Y Z} {S : Tensor Coeff U V W} (h : Restricts T S) :
    flatteningRank S ≤ flatteningRank T := by
  rcases h with ⟨a, b, c, rfl⟩
  unfold flatteningRank
  rw [firstFlattening_restrict]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

@[simp] theorem flatteningRank_zero [Fintype X] :
    flatteningRank (0 : Tensor Coeff X Y Z) = 0 := by
  exact Matrix.rank_zero

theorem flatteningRank_le_card [Fintype X] (T : Tensor Coeff X Y Z) :
    flatteningRank T ≤ Fintype.card X :=
  Matrix.rank_le_card_width _

/-- An identity minor certifies a lower bound directly from coefficients. -/
theorem card_le_flatteningRank_of_identity [Fintype X]
    {I : Type*} [Fintype I] [DecidableEq I]
    (T : Tensor Coeff X Y Z) (rows : I → Y × Z) (cols : I → X)
    (hidentity : ∀ i j, T (cols j) (rows i).1 (rows i).2 =
      if i = j then 1 else 0) :
    Fintype.card I ≤ flatteningRank T := by
  have heq : (firstFlattening T).submatrix rows cols = (1 : Matrix I I Coeff) := by
    funext i j
    exact hidentity i j
  have h := Matrix.rank_submatrix_le (firstFlattening T) rows cols
  rw [heq, Matrix.rank_one] at h
  exact h

@[simp] theorem flatteningRank_natTensor (n : ℕ) :
    flatteningRank (natTensor n) = n := by
  classical
  apply Nat.le_antisymm
  · simpa only [Fintype.card_fin] using flatteningRank_le_card (natTensor n)
  · have h := card_le_flatteningRank_of_identity (natTensor n)
      (fun i : Fin n => (i, i)) id (by
        intro i j
        simp [natTensor, eq_comm])
    simpa only [Fintype.card_fin] using h

/-- Flattening rank is bounded by every actual rank-one decomposition. -/
theorem flatteningRank_le_of_rankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor Coeff X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    flatteningRank T ≤ r := by
  have h' := flatteningRank_mono ((rankAtMost_iff_natTensor_restricts T r).mp h)
  simpa only [flatteningRank_natTensor] using h'

theorem flatteningRank_le_rank [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) : flatteningRank T ≤ rank T :=
  flatteningRank_le_of_rankAtMost (rank_spec T)

/-- The first-leg slices of a nonempty rectangular matrix multiplication tensor
are independent. The third matrix dimension supplies the selected common index. -/
theorem flatteningRank_matrixCoefficients
    {A B C : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [Nonempty C] :
    flatteningRank (Tensor.matrixCoefficients (K := Coeff) A B C) =
      Fintype.card A * Fintype.card B := by
  classical
  apply Nat.le_antisymm
  · simpa only [Fintype.card_prod] using
      flatteningRank_le_card (Tensor.matrixCoefficients (K := Coeff) A B C)
  · let c : C := Classical.choice inferInstance
    have h := card_le_flatteningRank_of_identity
      (Tensor.matrixCoefficients (K := Coeff) A B C)
      (fun i : A × B => ((i.2, c), (c, i.1))) id (by
        intro i j
        simp only [Tensor.matrixCoefficients, id_eq]
        split_ifs <;> simp_all [Prod.ext_iff])
    simpa only [Fintype.card_prod] using h

theorem flatteningRank_square (n : ℕ) :
    flatteningRank (Tensor.matrixCoefficients (K := Coeff) (Fin n) (Fin n) (Fin n)) =
      n ^ 2 := by
  by_cases hn : n = 0
  · subst n
    exact Nat.eq_zero_of_le_zero (by
      simpa using flatteningRank_le_card
        (Tensor.matrixCoefficients (K := Coeff) (Fin 0) (Fin 0) (Fin 0)))
  · let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    simpa only [Fintype.card_fin, pow_two] using
      (flatteningRank_matrixCoefficients (A := Fin n) (B := Fin n) (C := Fin n))

/-- Rows belonging to one summand embed into the full paired row family. -/
private def blockRows : (Y × Z) ⊕ (V × W) → (Y ⊕ V) × (Z ⊕ W)
  | .inl yz => (.inl yz.1, .inl yz.2)
  | .inr vw => (.inr vw.1, .inr vw.2)

/-- Insert the two diagonal row blocks and fill both cross row families by zero. -/
private def insertBlockRows [DecidableEq Y] [DecidableEq Z]
    [DecidableEq V] [DecidableEq W] :
    Matrix ((Y ⊕ V) × (Z ⊕ W)) ((Y × Z) ⊕ (V × W)) Coeff
  | (.inl y, .inl z), .inl yz => if yz = (y, z) then 1 else 0
  | (.inr v, .inr w), .inr vw => if vw = (v, w) then 1 else 0
  | _, _ => 0

/-- Ordinary matrix rank is additive on block diagonal matrices. This is a
statement about ranges of linear maps, with no tensor rank additivity premise. -/
theorem blockMatrix_rank {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n Coeff) (B : Matrix p q Coeff) :
    Matrix.rank (blockMatrix A B) = A.rank + B.rank := by
  have hblock : blockMatrix A B = Matrix.fromBlocks A 0 0 B := by
    funext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  rw [hblock]
  let e : (m ⊕ p → Coeff) ≃ₗ[Coeff] (m → Coeff) × (p → Coeff) :=
    LinearEquiv.sumArrowLequivProdArrow m p Coeff Coeff
  let d : (n ⊕ q → Coeff) ≃ₗ[Coeff] (n → Coeff) × (q → Coeff) :=
    LinearEquiv.sumArrowLequivProdArrow n q Coeff Coeff
  have hcomp :
      e.toLinearMap.comp (Matrix.fromBlocks A 0 0 B).mulVecLin =
        (A.mulVecLin.prodMap B.mulVecLin).comp d.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · funext i
      change ((Matrix.fromBlocks A 0 0 B).mulVecLin x) (Sum.inl i) =
        (A.mulVecLin (x ∘ Sum.inl)) i
      simp [Matrix.fromBlocks_mulVec]
    · funext i
      change ((Matrix.fromBlocks A 0 0 B).mulVecLin x) (Sum.inr i) =
        (B.mulVecLin (x ∘ Sum.inr)) i
      simp [Matrix.fromBlocks_mulVec]
  have hmap :
      (LinearMap.range (Matrix.fromBlocks A 0 0 B).mulVecLin).map e.toLinearMap =
        (LinearMap.range A.mulVecLin).prod (LinearMap.range B.mulVecLin) := by
    rw [← LinearMap.range_comp, hcomp, LinearEquiv.range_comp, LinearMap.range_prodMap]
  let ep :
      ((LinearMap.range A.mulVecLin).prod (LinearMap.range B.mulVecLin)) ≃ₗ[Coeff]
        (LinearMap.range A.mulVecLin) × (LinearMap.range B.mulVecLin) :=
    { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun := fun x => ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  calc
    (Matrix.fromBlocks A 0 0 B).rank =
        Module.finrank Coeff
          ((LinearMap.range A.mulVecLin).prod (LinearMap.range B.mulVecLin)) :=
      (e.ofSubmodules _ _ hmap).finrank_eq
    _ = Module.finrank Coeff
        ((LinearMap.range A.mulVecLin) × (LinearMap.range B.mulVecLin)) :=
      ep.finrank_eq
    _ = A.rank + B.rank := Module.finrank_prod

/-- The cross rows of a full tensor direct sum are all zero; removing exactly
these rows leaves the block diagonal matrix without changing its rank. -/
theorem flatteningRank_blockSum_eq_blockMatrix_rank
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor Coeff X Y Z) (S : Tensor Coeff U V W) :
    flatteningRank (blockSum T S) =
      Matrix.rank (blockMatrix (firstFlattening T) (firstFlattening S)) := by
  classical
  let D : Matrix ((Y × Z) ⊕ (V × W)) (X ⊕ U) Coeff :=
    blockMatrix (firstFlattening T) (firstFlattening S)
  have hsub : (firstFlattening (blockSum T S)).submatrix blockRows id = D := by
    funext yz x
    rcases yz with yz | vw <;> rcases x with x | u <;> rfl
  have hmul : insertBlockRows * D = firstFlattening (blockSum T S) := by
    funext yz x
    change (∑ j : (Y × Z) ⊕ (V × W), insertBlockRows yz j * D j x) =
      blockSum T S x yz.1 yz.2
    rcases yz with ⟨y, z⟩
    rcases y with y | v <;> rcases z with z | w <;> rcases x with x | u <;>
      simp [insertBlockRows, D, blockMatrix, firstFlattening,
        blockSum, Fintype.sum_sum_type, ite_mul]
  apply Nat.le_antisymm
  · change (firstFlattening (blockSum T S)).rank ≤ D.rank
    rw [← hmul]
    exact Matrix.rank_mul_le_right _ _
  · have h := Matrix.rank_submatrix_le (firstFlattening (blockSum T S)) blockRows id
    rw [hsub] at h
    exact h

theorem flatteningRank_blockSum [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor Coeff X Y Z) (S : Tensor Coeff U V W) :
    flatteningRank (blockSum T S) = flatteningRank T + flatteningRank S := by
  rw [flatteningRank_blockSum_eq_blockMatrix_rank]
  exact blockMatrix_rank _ _

end CoefficientTensor

namespace TensorRep

def flatteningRank (T : TensorRep) : ℕ := CoefficientTensor.flatteningRank T.coeff

theorem Restricts.flatteningRank_le {A B : TensorRep} (h : Restricts A B) :
    flatteningRank B ≤ flatteningRank A :=
  CoefficientTensor.flatteningRank_mono h

theorem Equivalent.flatteningRank_eq {A B : TensorRep} (h : Equivalent A B) :
    flatteningRank A = flatteningRank B :=
  Nat.le_antisymm h.2.flatteningRank_le h.1.flatteningRank_le

end TensorRep

namespace TensorClass

/-- Actual first-leg matrix rank, invariant under mutual tensor restriction. -/
def flatteningRank : TensorClass → ℕ :=
  Quotient.lift TensorRep.flatteningRank (fun _ _ h => h.flatteningRank_eq)

@[simp] theorem flatteningRank_ofRep (T : TensorRep) :
    flatteningRank (ofRep T) = T.flatteningRank := rfl

theorem flatteningRank_mono {A B : TensorClass} (h : A ≤ B) :
    flatteningRank A ≤ flatteningRank B := by
  induction A using Quotient.inductionOn with | h A =>
    induction B using Quotient.inductionOn with | h B =>
      exact TensorRep.Restricts.flatteningRank_le h

theorem flatteningRank_ofTensor {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor Coeff X Y Z) :
    flatteningRank (ofTensor T) = CoefficientTensor.flatteningRank T := by
  apply Nat.le_antisymm
  · exact CoefficientTensor.flatteningRank_mono (TensorRep.restricts_ofTensor T)
  · exact CoefficientTensor.flatteningRank_mono (TensorRep.ofTensor_restricts T)

theorem flatteningRank_le_rank (T : TensorClass) : flatteningRank T ≤ rank T := by
  induction T using Quotient.inductionOn with | h T =>
    exact CoefficientTensor.flatteningRank_le_rank T.coeff

end TensorClass
end OAI.LinearAlgebra.MatrixExponent.Upper
