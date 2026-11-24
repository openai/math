import OAI.Computability.VPVNP.RankCoordinateDimension

/-!
# Selecting Cramer columns by scanning the original matrix

Restricting row vectors to the first `s` coordinates is a linear map. Its
image takes the full row span and the span of the greedy basis to the same
space. Thus column-prefix ranks, including their first increases, can be
queried in the original matrix independently of the selected row indices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

variable {K : Type*} [Field K] [DecidableEq K] {n m : ℕ}

/-- Every column-prefix rank of the greedy row basis equals the corresponding
rank queried directly on the transpose of the original matrix. -/
theorem greedyRowBasis_columnPrefix_rank (A : Matrix (Fin n) (Fin m) K) (s : ℕ) (hs : s ≤ m) :
    rankQuery (prefixRows (greedyRowBasis A).transpose s hs) =
      rankQuery (prefixRows A.transpose s hs) := by
  let restrict : (Fin m → K) →ₗ[K] (Fin s → K) := LinearMap.funLeft K K (Fin.castLE hs)
  have h := congrArg (Submodule.map restrict) (greedyRowIndex_span A)
  rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp] at h
  rw [rankQuery_eq (prefixRows (greedyRowBasis A).transpose s hs), rankQuery_eq (prefixRows A.transpose s hs),
    Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  exact congrArg (fun S : Submodule K (Fin s → K) ↦ Module.finrank K S) h

/-- Appendix D's columns of the selected-row matrix have the very same
original indices as the independently selected greedy rows of the transpose. -/
theorem coordinateColumns_greedyRowBasis (A : Matrix (Fin n) (Fin m) K) (i : Fin (rankQuery A)) :
    coordinateColumns (greedyRowBasis A) (greedyRowBasis_fullRank A) i =
      greedyRowIndex A.transpose (Fin.cast (by rw [rankQuery_eq, rankQuery_eq, Matrix.rank_transpose]) i) := by
  let left := coordinateColumns (greedyRowBasis A) (greedyRowBasis_fullRank A) i
  let right := greedyRowIndex A.transpose (Fin.cast (by rw [rankQuery_eq, rankQuery_eq, Matrix.rank_transpose]) i)
  have before (s : ℕ) (hs : s ≤ m) : left.val < s ↔ right.val < s := by
    dsimp only [left, right, coordinateColumns]
    rw [greedyRowIndex_lt_iff _ _ s hs, greedyRowIndex_lt_iff _ _ s hs,
      greedyRowBasis_columnPrefix_rank A s hs]
    rfl
  have hl := (before (right.val+1) right.isLt).mpr (Nat.lt_succ_self _)
  have hr := (before (left.val+1) left.isLt).mp (Nat.lt_succ_self _)
  apply Fin.ext
  change left.val = right.val
  omega

/-- The Cramer query can use two independent base-matrix scans for its row
and column index sets. -/
theorem greedyCoordinateQuery_eq_baseColumns (A : Matrix (Fin n) (Fin m) K)
    (target : Fin m → K) (i : Fin (rankQuery A)) :
    greedyCoordinateQuery A target i = rowCoordinateQuery squareDetQuery (greedyRowBasis A)
      (fun j ↦ greedyRowIndex A.transpose (Fin.cast
        (by rw [rankQuery_eq, rankQuery_eq, Matrix.rank_transpose]) j)) target i := by
  rw [greedyCoordinateQuery, coordinateQuery, funext (coordinateColumns_greedyRowBasis A)]

/-- The sum defining the coordinate at a selected original row has one
contributing ordinal. -/
theorem originalRowCoordinate_at_greedy (A : Matrix (Fin n) (Fin m) K) (target : Fin m → K)
    (k : Fin (rankQuery A)) :
    originalRowCoordinate A target (greedyRowIndex A k) = greedyCoordinateQuery A target k := by
  simp [originalRowCoordinate, streamSum_eq, greedyRowIndex_eq]

open Stack.Coordinate (combinedOrdinal suffixBasisIndex_val)

/-- The selected suffix row, expressed in the combined row indexing. -/
theorem natAdd_suffixBasisIndex {w : ℕ} (W : Matrix (Fin w) (Fin m) K)
    (M : Matrix (Fin n) (Fin m) K) (i : Fin (suffixDimension W M)) :
    (suffixBasisIndex W M i).natAdd w = greedyRowIndex (appendRows W M) (combinedOrdinal W M i) := by
  let ordinal := combinedOrdinal W M i
  let g := greedyRowIndex (appendRows W M) ordinal
  have before := greedyRowIndex_lt_iff (appendRows W M) ordinal w (Nat.le_add_right _ _)
  have he : prefixRows (appendRows W M) w (Nat.le_add_right _ _) = W := by
    ext j c
    change appendRows W M (j.castAdd n) c = W j c
    rw [appendRows_left]
  rw [he] at before
  have ge : w ≤ g.val := by
    by_contra! h
    have hl := before.mp h
    change rankQuery W + i.val < rankQuery W at hl
    omega
  apply Fin.ext
  change w + (suffixBasisIndex W M i).val = g.val
  rw [suffixBasisIndex_val]
  change w + (g.val - w) = g.val
  omega

/-- For a queried basis monomial, Cramer's row ordinal is the rank of the
equation prefix plus its ordinal among the surviving monomials. -/
theorem quotientCoordinate_at_suffix {w : ℕ} (W : Matrix (Fin w) (Fin m) K)
    (M : Matrix (Fin n) (Fin m) K) (target : Fin m → K) (i : Fin (suffixDimension W M)) :
    quotientCoordinate W M target (suffixBasisIndex W M i) =
      greedyCoordinateQuery (appendRows W M) target (combinedOrdinal W M i) := by
  rw [quotientCoordinate, natAdd_suffixBasisIndex, originalRowCoordinate_at_greedy]

end RankQuery

end VPVNP
end Computability
end OAI
