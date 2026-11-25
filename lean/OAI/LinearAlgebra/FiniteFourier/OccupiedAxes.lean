import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization

/-! # Traversing the axes of an occupied group

A single axis acts on each fiber with the other coordinates fixed. Traversing
the axes multiplies those commuting matrices to give their tensor product.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
open scoped BigOperators

variable {K : Type*} [CommSemiring K] {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Type}
  [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

/-- Apply the chosen matrix along a single axis, leaving other coordinates fixed. -/
def axisMatrix (A : ∀ i, Matrix (P i) (P i) K) (i : ι) : Matrix (∀ k, P k) (∀ k, P k) K :=
  gridTensor (fun j => if j = i then A j else 1)

omit [∀ i, Fintype (P i)] in
/-- Splitting off an axis displays its action as a block diagonal matrix. -/
theorem axisMatrix_eq_blockDiagonal (A : ∀ i, Matrix (P i) (P i) K) (i : ι) :
    axisMatrix A i =
      (Matrix.blockDiagonal (fun _ : (∀ j : {j // j ≠ i}, P j.val) => A i)).submatrix
        (Equiv.piSplitAt i P) (Equiv.piSplitAt i P) := by
  classical
  ext x y
  rw [Matrix.submatrix_apply, Matrix.blockDiagonal_apply]
  change (∏ j, (if j = i then A j else 1) (x j) (y j)) =
    if (fun j : {j // j ≠ i} => x j.val) = (fun j : {j // j ≠ i} => y j.val)
      then A i (x i) (y i) else 0
  split_ifs with h
  · rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      have hxy : x j = y j := congrFun h ⟨j, hj⟩
      rw [ite_eq_right hj, hxy]
      exact Matrix.one_apply_eq _
    · simp
  · have he : ∃ j : {j // j ≠ i}, x j.val ≠ y j.val := by
      by_contra! he
      exact h (funext he)
    obtain ⟨⟨j, hj⟩, hxy⟩ := he
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj, hxy])

/-- Composing one step per axis on a common occupied workspace. -/
theorem layerWord_grid_traverse_workspace {V : Type} [Fintype V] [DecidableEq V]
    {d : ℕ} {A : ∀ i, Matrix (P i) (P i) K}
    (h : ∀ i, LayerWord d (Matrix.fromBlocks (axisMatrix A i) 0 0 (1 : Matrix V V K))) :
    LayerWord (Fintype.card ι * d) (Matrix.fromBlocks (gridTensor A) 0 0 (1 : Matrix V V K)) := by
  have hs (S : Finset ι) : LayerWord (S.card * d) (Matrix.fromBlocks
      (gridTensor fun i => if i ∈ S then A i else 1) 0 0 (1 : Matrix V V K)) := by
    induction S using Finset.induction_on with
    | empty => simpa [gridTensor_one] using (layerWord_one (I := (∀ i, P i) ⊕ V) (K := K) 0)
    | insert j S hj ih =>
      have hprod := layerWord_mul (h j) ih
      rw [Matrix.fromBlocks_multiply] at hprod
      simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.one_mul] at hprod
      rw [axisMatrix, ← gridTensor_mul] at hprod
      rw [Finset.card_insert_of_notMem hj, Nat.add_mul, Nat.one_mul, Nat.add_comm]
      convert hprod using 3
      funext i
      by_cases hij : i = j
      · subst i
        simp [hj]
      · simp [hij]
  simpa using hs Finset.univ

/-- Composing the in-place axis calls gives the tensor product on the original registers. -/
theorem layerWord_grid_traverse {d : ℕ} {A : ∀ i, Matrix (P i) (P i) K}
    (h : ∀ i, LayerWord d (axisMatrix A i)) :
    LayerWord (Fintype.card ι * d) (gridTensor A) := by
  have hs (S : Finset ι) : LayerWord (S.card * d)
      (gridTensor fun i => if i ∈ S then A i else 1) := by
    induction S using Finset.induction_on with
    | empty => simpa [gridTensor_one] using (layerWord_one (I := ∀ i, P i) (K := K) 0)
    | insert j S hj ih =>
      have hprod := layerWord_mul (h j) ih
      rw [axisMatrix, ← gridTensor_mul] at hprod
      rw [Finset.card_insert_of_notMem hj, Nat.add_mul, Nat.one_mul, Nat.add_comm]
      convert hprod using 2
      funext i
      by_cases hij : i = j
      · subst i
        simp [hj]
      · simp [hij]
  simpa using hs Finset.univ

/-- A group with at least `k` axes has `2^(k-1)` or more fibers along every axis,
so the synchronized occupied-fiber algorithm runs entirely on the group coordinates. -/
theorem layerWord_grid_block {W : ι → Type} [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]
    {d c k : ℕ} {A : ∀ i, Matrix (P i) (P i) K}
    (hc : 0 < c) (hck : c ≤ 2 ^ (k - 1)) (hk : k ≤ Fintype.card ι)
    (hr : Fintype.card ι ≤ 2 * k - 1) (ha : ∀ i, 2 ≤ Fintype.card (P i))
    (hw : ∀ i, Fintype.card (W i) ≤ Fintype.card (P i) * (c - 1))
    (h : ∀ i, LayerWord d (Matrix.fromBlocks (A i) 0 0 (1 : Matrix (W i) (W i) K))) :
    LayerWord ((2 * k - 1) * ((2 * c - 1) * d)) (gridTensor A) := by
  apply LayerWord.pad (Nat.mul_le_mul_right _ hr)
  apply layerWord_grid_traverse
  intro i
  rw [axisMatrix_eq_blockDiagonal]
  apply LayerWord.relabel (e := (Equiv.piSplitAt i P).symm)
  apply (h i).synchronizeOccupiedFibers hc _ (hw i)
  rw [Fintype.card_pi]
  calc
    c ≤ 2 ^ (k - 1) := hck
    _ ≤ 2 ^ (Fintype.card ι - 1) := Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hk _)
    _ = ∏ _ : {j // j ≠ i}, 2 := by simp [Fintype.card_subtype_compl]
    _ ≤ ∏ j : {j // j ≠ i}, Fintype.card (P j.val) :=
      Finset.prod_le_prod (fun j _ => ha j.val)

end FiniteFourier
end LinearAlgebra
end OAI
