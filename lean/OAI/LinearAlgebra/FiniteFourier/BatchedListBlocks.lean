import OAI.LinearAlgebra.FiniteFourier.BatchedListPrice

/-! # Additivity of list values across independent blocks -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical NNReal

variable {K : Type*} [Field K] {R C D E : Type}
    [Fintype R] [Fintype C] [Fintype D] [Fintype E]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))

private def legTriple {F : Fin 3 → Sort*} (a : F 0) (b : F 1) (c : F 2) : ∀ i, F i :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun i => i.elim0)))

omit [Fintype R] [Fintype C] [Fintype D] [Fintype E] in
private theorem list_reindex_entry (U : Matrix R C K) (r : D ≃ R) (c : E ≃ C)
    (i : D) (j k : E) :
    (if j = k then U (r i) (c j) else 0) = (if c j = c k then U (r i) (c j) else 0) := by
  simp

theorem listValue_reindex (U : Matrix R C K) (r : D ≃ R) (c : E ≃ C) :
    listValue φ (U.submatrix r c) = listValue φ U := by
  unfold listValue
  apply congrArg φ.val
  let e := legTriple (F := fun i => listLeg D E i ≃ listLeg R C i) r c c
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro z
  exact list_reindex_entry U r c (z 0) (z 1) (z 2)

private theorem mixed_sum_zero {A B : Fin 3 → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (y : ∀ i, A i ⊕ B i)
    (i j : Fin 3) (a : A i) (b : B j) (hi : y i = Sum.inl a) (hj : y j = Sum.inr b) :
    sumCoeff T U y = 0 := by
  apply sumCoeff_mixed
  · intro x he
    exact Sum.inl_ne_inr ((congrFun he j).trans hj)
  · intro x he
    exact Sum.inr_ne_inl ((congrFun he i).trans hi)

private theorem list_block_coeff (U : Matrix R C K) (V : Matrix D E K)
    (r : R ⊕ D) (a b : C ⊕ E) :
    (if a = b then (Matrix.fromBlocks U 0 0 V) r a else 0) =
    sumCoeff (A := listLeg R C) (B := listLeg D E) (listRaw U).coeff (listRaw V).coeff
      (legTriple (F := fun i => listLeg R C i ⊕ listLeg D E i) r a b) := by
  cases r with
  | inl r =>
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        simp only [Sum.inl.injEq, Matrix.fromBlocks_apply₁₁]
        refine (sumCoeff_inl (A := listLeg R C) (B := listLeg D E)
          (listRaw U).coeff (listRaw V).coeff (listCoordinates r a b)).symm.trans ?_
        apply congrArg (sumCoeff (A := listLeg R C) (B := listLeg D E)
          (listRaw U).coeff (listRaw V).coeff)
        funext i
        fin_cases i <;> rfl
      | inr b =>
        rw [ite_eq_right Sum.inl_ne_inr]
        exact (mixed_sum_zero _ _ _ 0 2 r b rfl rfl).symm
    | inr a =>
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, ite_self]
      exact (mixed_sum_zero _ _ _ 0 1 r a rfl rfl).symm
  | inr r =>
    cases a with
    | inl a =>
      simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, ite_self]
      exact (mixed_sum_zero _ _ _ 1 0 a r rfl rfl).symm
    | inr a =>
      cases b with
      | inl b =>
        rw [ite_eq_right Sum.inr_ne_inl]
        exact (mixed_sum_zero _ _ _ 2 0 b r rfl rfl).symm
      | inr b =>
        simp only [Sum.inr.injEq, Matrix.fromBlocks_apply₂₂]
        refine (sumCoeff_inr (A := listLeg R C) (B := listLeg D E)
          (listRaw U).coeff (listRaw V).coeff (listCoordinates r a b)).symm.trans ?_
        apply congrArg (sumCoeff (A := listLeg R C) (B := listLeg D E)
          (listRaw U).coeff (listRaw V).coeff)
        funext i
        fin_cases i <;> rfl

theorem listValue_fromBlocks (U : Matrix R C K) (V : Matrix D E K) :
    listValue φ (Matrix.fromBlocks U 0 0 V) = listValue φ U + listValue φ V := by
  let e := legTriple (F := fun i => listLeg (R ⊕ D) (C ⊕ E) i ≃
    listLeg R C i ⊕ listLeg D E i) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
  unfold listValue
  rw [← φ.2.2.2.1, ← ofRaw_add]
  apply congrArg φ.val
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro z
  have he : (fun i => e i (z i)) =
      legTriple (F := fun i => listLeg R C i ⊕ listLeg D E i) (z 0) (z 1) (z 2) := by
    funext i
    fin_cases i <;> rfl
  refine Eq.trans ?_ ((list_block_coeff U V (z 0) (z 1) (z 2)).trans
    (congrArg (sumCoeff (A := listLeg R C) (B := listLeg D E)
      (listRaw U).coeff (listRaw V).coeff) he.symm))
  unfold listRaw
  dsimp only
  congr 1

private def splitFirstBlock (R : Type) (J : ℕ) : R ⊕ (R × Fin J) ≃ R × Fin (J+1) where
  toFun := Sum.elim (fun r => (r, 0)) (fun p => (p.1, p.2.succ))
  invFun p := Fin.cases (.inl p.1) (fun j => .inr (p.1, j)) p.2
  left_inv p := by rcases p with r | ⟨r,j⟩ <;> simp
  right_inv p := by rcases p with ⟨r,j⟩; cases j using Fin.cases <;> simp

theorem listValue_blockDiagonal {J : ℕ} (U : Fin J → Matrix R C K) :
    listValue φ (Matrix.blockDiagonal U) = ∑ j, listValue φ (U j) := by
  induction J with
  | zero =>
    have he : Matrix.blockDiagonal U = 0 := by ext ⟨_, j⟩; exact j.elim0
    rw [he, listValue_zero]
    simp
  | succ J ih =>
    have he : (Matrix.blockDiagonal U).submatrix (splitFirstBlock R J) (splitFirstBlock C J) =
        Matrix.fromBlocks (U 0) 0 0 (Matrix.blockDiagonal (fun j => U (Fin.succ j))) := by
      ext r c
      rcases r with r | ⟨r,i⟩ <;> rcases c with c | ⟨c,j⟩ <;>
        simp [splitFirstBlock, Matrix.blockDiagonal_apply, Ne.symm (Fin.succ_ne_zero _)]
    rw [← listValue_reindex φ (Matrix.blockDiagonal U) (splitFirstBlock R J) (splitFirstBlock C J),
      he, listValue_fromBlocks, ih, Fin.sum_univ_succ]

end FiniteFourier
end LinearAlgebra
end OAI
