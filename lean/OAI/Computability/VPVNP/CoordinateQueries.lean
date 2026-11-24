import OAI.Computability.VPVNP.DeterminantQueries

/-!
# Greedy row and column coordinate queries

Appendix D.2 of *VP and VNP differ over every field* selects rows using ranks
of prefixes of the original matrix. For an independent list of rows it
selects independent columns by the same test on the transpose. A coordinate
of a target in their span then uses two ordinary determinant queries.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

open Polynomial

/-- Ordinary determinant recovered at the top pencil degree, with its sign. -/
def squareDetQuery {K : Type*} [CommRing K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K) : K :=
  (-1) ^ r * determinantQuery (fun i j z => if z = 0 then A i j else 0) r 0

theorem squareDetQuery_eq {K : Type*} [Field K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K) :
    squareDetQuery A = A.det := by
  let M := A.map C
  have he (i j : Fin r) (z : ℕ) : (if z = 0 then A i j else 0) = (M i j).coeff z := by
    simp [M, coeff_C]
  have htop : M.charpolyRev.coeff r = M.charpoly.coeff 0 := by
    rw [← M.reverse_charpoly, coeff_reverse, M.charpoly_natDegree_eq_dim, Fintype.card_fin]
    simp
  rw [squareDetQuery, determinantQuery_eq M _ he, htop]
  have hs := M.det_eq_sign_charpoly_coeff
  rw [Fintype.card_fin, ← show C ((-1 : K) ^ r) = (-1 : K[X]) ^ r from by simp] at hs
  have h := congrArg (fun p : K[X] => p.coeff 0) hs
  rw [coeff_C_mul] at h
  change (C.mapMatrix A).det.coeff 0 = _ at h
  rw [← C.map_det, coeff_C_zero] at h
  exact h.symm

variable {K : Type*} [Field K] {n m r : ℕ}

/-- The first `s` rows, retaining every column. -/
def prefixRows (A : Matrix (Fin n) (Fin m) K) (s : ℕ) (hs : s ≤ n) :
    Matrix (Fin s) (Fin m) K := A.submatrix (Fin.castLE hs) id

theorem rank_prefixRows (A : Matrix (Fin n) (Fin m) K) (s : ℕ) (hs : s ≤ n) :
    (prefixRows A s hs).rank = ((greedyIndices K A.row).filter (fun i => i.val < s)).card := by
  let S := (greedyIndices K A.row).filter (fun i => i.val < s)
  have hS : (S : Set (Fin n)) = (greedyIndices K A.row : Set (Fin n)) ∩ {i | i.val < s} := by
    ext i
    simp [S]
  have h := greedyIndices_prefix K A.row s
  rw [← hS] at h
  have hrows : (prefixRows A s hs).row = A.row ∘ Fin.castLE hs := rfl
  rw [Matrix.rank_eq_finrank_span_row, hrows, Set.range_comp, Fin.range_castLE, ← h.2,
    Set.image_eq_range, finrank_span_eq_card h.1]
  simp [S]

/-- The next row is retained exactly at the indices where the prefix rank increases. -/
theorem mem_greedyIndices_iff_prefixRank_lt (A : Matrix (Fin n) (Fin m) K) (i : Fin n) :
    i ∈ greedyIndices K A.row ↔
      (prefixRows A i.val i.isLt.le).rank < (prefixRows A (i.val + 1) i.isLt).rank := by
  rw [rank_prefixRows, rank_prefixRows]
  let S := greedyIndices K A.row
  have hsplit : S.filter (fun j => j.val < i.val + 1) =
      if i ∈ S then insert i (S.filter (fun j => j.val < i.val))
      else S.filter (fun j => j.val < i.val) := by
    ext j
    by_cases hi : i ∈ S <;> simp only [hi, ite_true, ite_false, Finset.mem_filter, Finset.mem_insert]
    · by_cases he : j = i
      · subst j; simp [hi]
      · have hval : j.val ≠ i.val := Fin.val_injective.ne he
        simp [he]; omega
    · apply and_congr_right
      intro hj
      have hval : j.val ≠ i.val := fun he => hi (Fin.ext he ▸ hj)
      omega
  change i ∈ S ↔ (S.filter _).card < (S.filter _).card
  rw [hsplit]
  by_cases hi : i ∈ S <;> simp [hi]

private theorem ordered_prefix_counts {n r : ℕ} (S : Finset (Fin n)) (hcard : S.card = r)
    (k : Fin r) :
    (S.filter (· < S.orderEmbOfFin hcard k)).card = k.val ∧
      (S.filter (· ≤ S.orderEmbOfFin hcard k)).card = k.val + 1 := by
  let e := S.orderEmbOfFin hcard
  have hlt : S.filter (· < e k) = (Finset.Iio k).map e.toEmbedding := by
    conv_lhs => rhs; rw [← S.map_orderEmbOfFin_univ hcard]
    rw [Finset.filter_map]
    congr 1
    ext i
    rw [Finset.mem_filter]
    change (i ∈ Finset.univ ∧ e i < e k) ↔ _
    simp
  have hle : S.filter (· ≤ e k) = (Finset.Iic k).map e.toEmbedding := by
    conv_lhs => rhs; rw [← S.map_orderEmbOfFin_univ hcard]
    rw [Finset.filter_map]
    congr 1
    ext i
    rw [Finset.mem_filter]
    change (i ∈ Finset.univ ∧ e i ≤ e k) ↔ _
    simp
  change (S.filter (· < e k)).card = _ ∧ (S.filter (· ≤ e k)).card = _
  simp [hlt, hle]

/-- Retrieve the zero-based `k`-th selected index by scanning prefixes
until the number of selected items first exceeds `k`. -/
def firstPrefixAbove {n : ℕ} (prefixRank : (s : ℕ) → s ≤ n → ℕ) (k : ℕ)
    (hex : ∃ i : Fin n, k < prefixRank (i.val + 1) i.isLt) : Fin n :=
  Fin.find (fun i => k < prefixRank (i.val + 1) i.isLt) hex

theorem prefix_above_exists {n r : ℕ} (S : Finset (Fin n)) (hcard : S.card = r)
    (prefixRank : (s : ℕ) → s ≤ n → ℕ)
    (hrank : ∀ s hs, prefixRank s hs = (S.filter (fun i => i.val < s)).card) (k : Fin r) :
    ∃ i : Fin n, k.val < prefixRank (i.val + 1) i.isLt := by
  let j := S.orderEmbOfFin hcard k
  refine ⟨j, ?_⟩
  rw [hrank]
  simp only [Nat.lt_succ_iff]
  change k.val < (S.filter (· ≤ j)).card
  rw [(ordered_prefix_counts S hcard k).2]
  omega

theorem firstPrefixAbove_eq {n r : ℕ} (S : Finset (Fin n)) (hcard : S.card = r)
    (prefixRank : (s : ℕ) → s ≤ n → ℕ)
    (hrank : ∀ s hs, prefixRank s hs = (S.filter (fun i => i.val < s)).card) (k : Fin r) :
    firstPrefixAbove prefixRank k.val (prefix_above_exists S hcard prefixRank hrank k) =
      S.orderEmbOfFin hcard k := by
  apply (Fin.find_eq_iff _).mpr
  obtain ⟨hlt, hle⟩ := ordered_prefix_counts S hcard k
  constructor
  · rw [hrank]
    simp only [Nat.lt_succ_iff]
    change k.val < (S.filter (· ≤ S.orderEmbOfFin hcard k)).card
    omega
  · intro i hi
    rw [hrank, not_lt, ← hlt]
    apply Finset.card_le_card
    intro j hj
    obtain ⟨hjS, hji⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hjS, lt_of_le_of_lt (Nat.le_of_lt_succ hji) hi⟩


/-- Query one coordinate in a row basis from an oracle for square determinants.
Both input matrices are given entrywise, from the selected columns. -/
def rowCoordinateQuery (detQuery : Matrix (Fin r) (Fin r) K → K)
    (B : Matrix (Fin r) (Fin m) K) (cols : Fin r → Fin m) (target : Fin m → K) (i : Fin r) : K :=
  let A := B.submatrix id cols
  detQuery (A.updateRow i (target ∘ cols)) / detQuery A

/-- Replacing row `i` by the restricted target multiplies the determinant by
the `i`-th coefficient in every representation of that target. -/
theorem rowCoordinateQuery_eq (detQuery : Matrix (Fin r) (Fin r) K → K)
    (hdet : ∀ A, detQuery A = A.det) (B : Matrix (Fin r) (Fin m) K)
    (cols : Fin r → Fin m) (hnonsing : (B.submatrix id cols).det ≠ 0)
    (target : Fin m → K) (c : Fin r → K) (hc : ∑ k, c k • B k = target) (i : Fin r) :
    rowCoordinateQuery detQuery B cols target i = c i := by
  let A := B.submatrix id cols
  have hrestrict : target ∘ cols = ∑ k, c k • A k := by
    funext j
    rw [← hc, Function.comp_apply, Finset.sum_apply, Finset.sum_apply]
    rfl
  change detQuery (A.updateRow i (target ∘ cols)) / detQuery A = c i
  rw [hdet, hdet, hrestrict, Matrix.det_updateRow_sum, smul_eq_mul, mul_div_cancel_right₀ _ hnonsing]

/-- When the target lies in the span, querying the coordinates reconstructs
the target on all columns of the original rectangular matrix. -/
theorem rowCoordinateQuery_reconstruct (detQuery : Matrix (Fin r) (Fin r) K → K)
    (hdet : ∀ A, detQuery A = A.det) (B : Matrix (Fin r) (Fin m) K)
    (cols : Fin r → Fin m) (hnonsing : (B.submatrix id cols).det ≠ 0)
    (target : Fin m → K) (hspan : target ∈ Submodule.span K (Set.range B)) :
    ∑ i, rowCoordinateQuery detQuery B cols target i • B i = target := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hspan
  simpa only [rowCoordinateQuery_eq detQuery hdet B cols hnonsing target c hc] using hc

section GreedyQueries

variable [DecidableEq K]

theorem greedyRows_card (A : Matrix (Fin n) (Fin m) K) :
    (greedyIndices K A.row).card = rankQuery A := by
  rw [rankQuery_eq]
  have h := rank_prefixRows A n le_rfl
  have hA : prefixRows A n le_rfl = A := rfl
  rw [hA] at h
  simpa using h.symm

private theorem prefixRankQuery_count (A : Matrix (Fin n) (Fin m) K) (s : ℕ) (hs : s ≤ n) :
    rankQuery (prefixRows A s hs) = ((greedyIndices K A.row).filter (fun i => i.val < s)).card := by
  rw [rankQuery_eq, rank_prefixRows]

/-- The indexed row of the greedy basis. Every rank query during the scan
uses an initial block of the supplied matrix. -/
def greedyRowIndex (A : Matrix (Fin n) (Fin m) K) (k : Fin (rankQuery A)) : Fin n :=
  firstPrefixAbove (fun s hs => rankQuery (prefixRows A s hs)) k.val
    (prefix_above_exists _ (greedyRows_card A) _ (prefixRankQuery_count A) k)

theorem greedyRowIndex_eq (A : Matrix (Fin n) (Fin m) K) (k : Fin (rankQuery A)) :
    greedyRowIndex A k = (greedyIndices K A.row).orderEmbOfFin (greedyRows_card A) k :=
  firstPrefixAbove_eq _ (greedyRows_card A) _ (prefixRankQuery_count A) k

theorem greedyRowIndex_independent (A : Matrix (Fin n) (Fin m) K) :
    LinearIndependent K (A.row ∘ greedyRowIndex A) := by
  have h := greedyIndices_linearIndepOn K A.row
  let e := (greedyIndices K A.row).orderIsoOfFin (greedyRows_card A)
  have h' := (linearIndependent_equiv (R := K)
    (f := fun i : greedyIndices K A.row => A.row i.val) e.toEquiv).mpr h
  change LinearIndependent K
    (fun i => A.row ((greedyIndices K A.row).orderIsoOfFin (greedyRows_card A) i).val) at h'
  simpa only [Function.comp_def, greedyRowIndex_eq, Finset.coe_orderIsoOfFin_apply] using h'

theorem greedyRowIndex_span (A : Matrix (Fin n) (Fin m) K) :
    Submodule.span K (Set.range (A.row ∘ greedyRowIndex A)) =
      Submodule.span K (Set.range A.row) := by
  have hindices : greedyRowIndex A = (greedyIndices K A.row).orderEmbOfFin (greedyRows_card A) :=
    funext (greedyRowIndex_eq A)
  rw [hindices, Set.range_comp, Finset.range_orderEmbOfFin]
  simpa using greedyIndices_span_prefix K A.row n

/-- The independent columns of an assembled full-row-rank matrix, queried
by their ordinal among the selected columns. -/
def coordinateColumns (B : Matrix (Fin r) (Fin m) K) (hB : B.rank = r) : Fin r → Fin m :=
  fun i => greedyRowIndex B.transpose (Fin.cast (by rw [rankQuery_eq, Matrix.rank_transpose, hB]) i)

theorem coordinateColumns_nonsingular (B : Matrix (Fin r) (Fin m) K) (hB : B.rank = r) :
    (B.submatrix id (coordinateColumns B hB)).det ≠ 0 := by
  have hdim : r = rankQuery B.transpose := by rw [rankQuery_eq, Matrix.rank_transpose, hB]
  let e := finCongr hdim
  have h := greedyRowIndex_independent B.transpose
  have h' := (linearIndependent_equiv (R := K)
    (f := B.transpose.row ∘ greedyRowIndex B.transpose) e).mpr h
  have hc : LinearIndependent K (B.submatrix id (coordinateColumns B hB)).col := h'
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hc)).ne_zero

/-- Coordinate of the target row in an independent row list, using only
entrywise prefix rank queries and two scalar determinant queries. -/
def coordinateQuery (B : Matrix (Fin r) (Fin m) K) (hB : B.rank = r)
    (target : Fin m → K) (i : Fin r) : K :=
  rowCoordinateQuery squareDetQuery B (coordinateColumns B hB) target i

theorem coordinateQuery_eq (B : Matrix (Fin r) (Fin m) K) (hB : B.rank = r)
    (target : Fin m → K) (c : Fin r → K) (hc : ∑ k, c k • B k = target) (i : Fin r) :
    coordinateQuery B hB target i = c i :=
  rowCoordinateQuery_eq _ squareDetQuery_eq _ _ (coordinateColumns_nonsingular B hB) _ c hc i

theorem coordinateQuery_reconstruct (B : Matrix (Fin r) (Fin m) K) (hB : B.rank = r)
    (target : Fin m → K) (hspan : target ∈ Submodule.span K (Set.range B)) :
    ∑ i, coordinateQuery B hB target i • B i = target :=
  rowCoordinateQuery_reconstruct _ squareDetQuery_eq _ _ (coordinateColumns_nonsingular B hB) _ hspan

/-- The rectangular matrix of the selected rows, still presented by an entry
function so querying its entries only requests their indices in the original matrix. -/
def greedyRowBasis (A : Matrix (Fin n) (Fin m) K) : Matrix (Fin (rankQuery A)) (Fin m) K :=
  A.submatrix (greedyRowIndex A) id

theorem greedyRowBasis_fullRank (A : Matrix (Fin n) (Fin m) K) :
    (greedyRowBasis A).rank = rankQuery A := by
  have h : LinearIndependent K (greedyRowBasis A).row := greedyRowIndex_independent A
  simpa using h.rank_matrix

/-- Coordinate of a target in the greedy row basis of an arbitrary matrix. -/
def greedyCoordinateQuery (A : Matrix (Fin n) (Fin m) K) (target : Fin m → K)
    (i : Fin (rankQuery A)) : K :=
  coordinateQuery (greedyRowBasis A) (greedyRowBasis_fullRank A) target i

theorem greedyCoordinateQuery_reconstruct (A : Matrix (Fin n) (Fin m) K)
    (target : Fin m → K) (hspan : target ∈ Submodule.span K (Set.range A.row)) :
    ∑ i, greedyCoordinateQuery A target i • A (greedyRowIndex A i) = target := by
  rw [← greedyRowIndex_span A] at hspan
  exact coordinateQuery_reconstruct (greedyRowBasis A) (greedyRowBasis_fullRank A) target hspan

end GreedyQueries

end RankQuery

end VPVNP
end Computability
end OAI
