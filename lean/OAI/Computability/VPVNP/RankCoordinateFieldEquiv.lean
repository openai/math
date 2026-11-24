import OAI.Computability.VPVNP.CoordinateQueries
import OAI.Computability.VPVNP.RankQueryStackInterpretation

/-!
# Transport of greedy coordinate queries across the advised field isomorphism

Every prefix rank is preserved when entries are mapped into an isomorphic
field. The two greedy scans therefore select the same physical indices. The
quotient of the two determinants then transports entrywise, for arbitrary
target rows.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

variable {L F : Type*} [Field L] [Field F] [DecidableEq L] [DecidableEq F] {n m r : ℕ}

/-- The physical rank scan commutes with interpretation into an isomorphic field. -/
theorem rankQuery_map_eq (φ : L ≃+* F) (M : Matrix (Fin n) (Fin m) L) :
    rankQuery (M.map φ) = rankQuery M := by
  rw [rankQuery_eq, rankQuery_eq]
  exact (Stack.SchurKey.computeRank_interpreted φ.toRingHom φ.injective M).symm.trans
    (Stack.SchurKey.computeRank_eq M)

private theorem firstPrefixAbove_congr (f g : (s : ℕ) → s ≤ n → ℕ) (h : f = g) (k : ℕ)
    (hf : ∃ i : Fin n, k < f (i.val+1) i.isLt) (hg : ∃ i : Fin n, k < g (i.val+1) i.isLt) :
    firstPrefixAbove f k hf = firstPrefixAbove g k hg := by
  subst g
  rfl

/-- A prefix-rank increase occurs at the same original row after mapping
the field. Casts identify only the two bounds on the dense ordinal. -/
theorem greedyRowIndex_map (φ : L ≃+* F) (M : Matrix (Fin n) (Fin m) L)
    (i : Fin (rankQuery (M.map φ))) :
    greedyRowIndex (M.map φ) i = greedyRowIndex M (Fin.cast (rankQuery_map_eq φ M) i) := by
  unfold greedyRowIndex
  apply firstPrefixAbove_congr
  funext s hs
  exact rankQuery_map_eq φ (prefixRows M s hs)

/-- The two assembled row bases agree entrywise under the field map. -/
theorem greedyRowBasis_map_apply (φ : L ≃+* F) (M : Matrix (Fin n) (Fin m) L)
    (i : Fin (rankQuery (M.map φ))) (j : Fin m) :
    greedyRowBasis (M.map φ) i j = φ (greedyRowBasis M (Fin.cast (rankQuery_map_eq φ M) i) j) := by
  change φ (M (greedyRowIndex (M.map φ) i) j) = φ (M _ j)
  rw [greedyRowIndex_map]

/-- On a full-row-rank matrix the transpose prefix scan selects the same columns. -/
theorem coordinateColumns_map (φ : L ≃+* F) (B : Matrix (Fin r) (Fin m) L)
    (h : B.rank = r) (h' : (B.map φ).rank = r) (i : Fin r) :
    coordinateColumns (B.map φ) h' i = coordinateColumns B h i := by
  unfold coordinateColumns
  exact greedyRowIndex_map φ B.transpose _

private theorem columns_cast {r' : ℕ} (φ : L ≃+* F) (eq : r' = r)
    (B : Matrix (Fin r) (Fin m) L) (D : Matrix (Fin r') (Fin m) F)
    (mapped : ∀ i j, D i j = φ (B (Fin.cast eq i) j)) (h : B.rank = r) (h' : D.rank = r')
    (i : Fin r') : coordinateColumns D h' i = coordinateColumns B h (Fin.cast eq i) := by
  subst r'
  have he : D = B.map φ := Matrix.ext mapped
  subst D
  exact coordinateColumns_map φ B h h' i

/-- Columns selected from the already selected rows commute with the
isomorphism, including when the original matrix is rectangular or singular. -/
theorem greedyColumns_map (φ : L ≃+* F) (M : Matrix (Fin n) (Fin m) L)
    (i : Fin (rankQuery (M.map φ))) :
    coordinateColumns (greedyRowBasis (M.map φ)) (greedyRowBasis_fullRank _) i =
      coordinateColumns (greedyRowBasis M) (greedyRowBasis_fullRank _) (Fin.cast (rankQuery_map_eq φ M) i) :=
  columns_cast φ (rankQuery_map_eq φ M) _ _ (greedyRowBasis_map_apply φ M) _ _ i

omit [DecidableEq L] [DecidableEq F] in
/-- Replacing the target row and dividing the two determinants commute
with the field map, even for targets outside the selected rows' span. -/
theorem rowCoordinateQuery_map (φ : L ≃+* F) (B : Matrix (Fin r) (Fin m) L) (cols : Fin r → Fin m)
    (target : Fin m → L) (i : Fin r) :
    rowCoordinateQuery squareDetQuery (B.map φ) cols (φ ∘ target) i =
      φ (rowCoordinateQuery squareDetQuery B cols target i) := by
  simp only [rowCoordinateQuery, squareDetQuery_eq, map_div₀]
  let D := B.submatrix id cols
  change ((D.map φ).updateRow i ((φ ∘ target) ∘ cols)).det / (D.map φ).det =
    φ ((D.updateRow i (target ∘ cols)).det) / φ D.det
  have hn := φ.toRingHom.map_det (D.updateRow i (target ∘ cols))
  have hd := φ.toRingHom.map_det D
  change φ ((D.updateRow i (target ∘ cols)).det) = ((D.updateRow i (target ∘ cols)).map φ).det at hn
  rw [Matrix.map_updateRow] at hn
  rw [hn, show φ D.det = (D.map φ).det from hd]
  rfl

private theorem coordinate_cast {r' : ℕ} (φ : L ≃+* F) (eq : r' = r)
    (B : Matrix (Fin r) (Fin m) L) (D : Matrix (Fin r') (Fin m) F)
    (mapped : ∀ i j, D i j = φ (B (Fin.cast eq i) j)) (h : B.rank = r) (h' : D.rank = r')
    (target : Fin m → L) (i : Fin r') :
    coordinateQuery D h' (φ ∘ target) i = φ (coordinateQuery B h target (Fin.cast eq i)) := by
  subst r'
  have he : D = B.map φ := Matrix.ext mapped
  subst D
  unfold coordinateQuery
  rw [show coordinateColumns (B.map φ) h' = coordinateColumns B h from funext (coordinateColumns_map φ B h h')]
  exact rowCoordinateQuery_map φ B _ target i

/-- The physical greedy coordinate over the advised representation maps to
the corresponding coordinate over the represented field. -/
theorem greedyCoordinateQuery_map (φ : L ≃+* F) (M : Matrix (Fin n) (Fin m) L)
    (target : Fin m → L) (i : Fin (rankQuery (M.map φ))) :
    greedyCoordinateQuery (M.map φ) (φ ∘ target) i =
      φ (greedyCoordinateQuery M target (Fin.cast (rankQuery_map_eq φ M) i)) :=
  coordinate_cast φ (rankQuery_map_eq φ M) _ _ (greedyRowBasis_map_apply φ M) _ _ target i

end RankQuery

end VPVNP
end Computability
end OAI
