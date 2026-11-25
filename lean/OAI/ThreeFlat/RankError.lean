import Mathlib.LinearAlgebra.Matrix.Rank

namespace OAI
/-! # Rank errors in folded computations

Replacing slices in a chronological product costs at most the sum of their
rank errors. The same estimate survives the sum over parent transcripts and
the restriction to external matrix indices. -/

namespace ThreeFlat

open scoped BigOperators

variable {F n : Type*} [Field F] [Fintype n]

private theorem rank_add_le {m : Type*} [Fintype m] (A B : Matrix m n F) :
    (A + B).rank ≤ A.rank + B.rank := by
  have h := Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)
  have upper := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  change Module.finrank F (LinearMap.range (A + B).mulVecLin) ≤ _
  rw [Matrix.mulVecLin_add]
  exact h.trans upper

/-- Matrix rank is subadditive on a finite family of summands. -/
theorem matrix_rank_sum_le {ι m : Type*} [Fintype m] (s : Finset ι) (A : ι → Matrix m n F) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- Errors in successive matrix factors add, irrespective of their ranks or singularity. -/
theorem rank_sub_prod_le [DecidableEq n] {ι : Type*}
    (s : List ι) (A B : ι → Matrix n n F) :
    ((s.map A).prod - (s.map B).prod).rank ≤ (s.map fun i => (A i - B i).rank).sum := by
  induction s with
  | nil => simp
  | cons i s ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have split : A i * (s.map A).prod - B i * (s.map B).prod =
        (A i - B i) * (s.map A).prod + B i * ((s.map A).prod - (s.map B).prod) := by
      rw [sub_mul, mul_sub]
      rw [sub_add_sub_cancel]
    rw [split]
    exact (rank_add_le _ _).trans (Nat.add_le_add (Matrix.rank_mul_le_left _ _)
      ((Matrix.rank_mul_le_right _ _).trans ih))

/-- For an operation with finitely many parent transcripts, scalar weights and
cancellation among transcripts cannot increase the sum of the slice error bounds. -/
theorem rank_sub_weighted_transcripts_le [DecidableEq n] {ι τ : Type*}
    (parents : Finset τ) (weight : τ → F) (slices : τ → List ι)
    (A B : τ → ι → Matrix n n F) :
    ((∑ t ∈ parents, weight t • ((slices t).map (A t)).prod) -
      ∑ t ∈ parents, weight t • ((slices t).map (B t)).prod).rank ≤
      ∑ t ∈ parents, ((slices t).map fun i => (A t i - B t i).rank).sum := by
  rw [← Finset.sum_sub_distrib]
  refine (matrix_rank_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro t _
  rw [← smul_sub]
  by_cases hz : weight t = 0
  · simp [hz]
  · rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hz)]
    exact rank_sub_prod_le _ _ _

/-- In a fold on `bits` memory bits, naming the parent transcript and the slice
spends at most the sum of their encoding lengths from the per-slice rank deficit. -/
theorem fold_rank_deficit [DecidableEq n] {ι τ : Type*}
    (parents : Finset τ) (weight : τ → F) (slices : τ → List ι)
    (A B : τ → ι → Matrix n n F) (bits loss transcriptBits sliceBits : ℕ)
    (fits : loss ≤ bits) (short : transcriptBits + sliceBits ≤ loss)
    (count : parents.card ≤ 2 ^ transcriptBits)
    (lengths : ∀ t ∈ parents, (slices t).length ≤ 2 ^ sliceBits)
    (discard : ∀ t ∈ parents, ∀ i ∈ slices t, (A t i - B t i).rank ≤ 2 ^ (bits - loss)) :
    ((∑ t ∈ parents, weight t • ((slices t).map (A t)).prod) -
      ∑ t ∈ parents, weight t • ((slices t).map (B t)).prod).rank ≤
      2 ^ (bits - (loss - (transcriptBits + sliceBits))) := by
  have boundedSum (l : List ι) (f : ι → ℕ) (d : ℕ) (hb : ∀ i ∈ l, f i ≤ d) :
      (l.map f).sum ≤ l.length * d := by
    induction l with
    | nil => simp
    | cons i rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      rw [Nat.add_comm (rest.length * d)]
      exact Nat.add_le_add (hb i (by simp)) (ih fun j hj => hb j (by simp [hj]))
  have oneParent (t : τ) (ht : t ∈ parents) :
      ((slices t).map fun i => (A t i - B t i).rank).sum ≤
        2 ^ sliceBits * 2 ^ (bits - loss) :=
    (boundedSum _ _ _ (discard t ht)).trans (Nat.mul_le_mul_right _ (lengths t ht))
  calc
    _ ≤ _ := rank_sub_weighted_transcripts_le parents weight slices A B
    _ ≤ ∑ _t ∈ parents, 2 ^ sliceBits * 2 ^ (bits - loss) := Finset.sum_le_sum oneParent
    _ = parents.card * (2 ^ sliceBits * 2 ^ (bits - loss)) := by simp
    _ ≤ 2 ^ transcriptBits * (2 ^ sliceBits * 2 ^ (bits - loss)) := Nat.mul_le_mul_right _ count
    _ = 2 ^ (bits - (loss - (transcriptBits + sliceBits))) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega

/-- Rank deficits for consecutive folding and banking operations accumulate additively.
An exact operation contributes zero, since its successive matrices agree. -/
theorem rank_sub_stages_le (A : ℕ → Matrix n n F) (k : ℕ) :
    (A 0 - A k).rank ≤ ∑ i ∈ Finset.range k, (A i - A (i + 1)).rank := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← sub_add_sub_cancel (A 0) (A k) (A (k + 1))]
    exact (rank_add_le _ _).trans (Nat.add_le_add_right ih _)

/-- A product of blocks, each obtained by summing the matrices for all its fixings,
retains the rank bound when auxiliary input and output indices are fixed. -/
theorem rank_sub_restricted_blocks_le [DecidableEq n] {ι β m : Type*} [Fintype m]
    (blocks : List ι) (fixings : ι → Finset β) (A B : ι → β → Matrix n n F)
    (rows cols : m → n) :
    (((blocks.map fun i => ∑ j ∈ fixings i, A i j).prod.submatrix rows cols) -
     ((blocks.map fun i => ∑ j ∈ fixings i, B i j).prod.submatrix rows cols)).rank ≤
      (blocks.map fun i => ∑ j ∈ fixings i, (A i j - B i j).rank).sum := by
  let original := fun i => ∑ j ∈ fixings i, A i j
  let replacement := fun i => ∑ j ∈ fixings i, B i j
  change (((blocks.map original).prod - (blocks.map replacement).prod).submatrix rows cols).rank ≤ _
  refine (Matrix.rank_submatrix_le _ rows cols).trans
    ((rank_sub_prod_le blocks original replacement).trans ?_)
  dsimp only [original, replacement]
  induction blocks with
  | nil => simp
  | cons i rest ih =>
    simp only [List.map_cons, List.sum_cons]
    refine Nat.add_le_add ?_ ih
    rw [← Finset.sum_sub_distrib]
    exact matrix_rank_sum_le _ _

end ThreeFlat

end OAI
