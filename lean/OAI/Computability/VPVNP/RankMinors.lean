import OAI.Computability.VPVNP.ShiftedPairing

/-!
# Support of maximal minors

Appendix D.2 of *VP and VNP differ over every field* uses the fact that the
nonzero minors of order equal to the rank have independently chosen row and
column bases. All minors of larger order vanish.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

open Set
open Set.powersetCard
open VPVNP.Crossing

variable {K : Type*} [Field K] {n m q : ℕ}

private theorem det_submatrix_ne_zero_iff (M : Matrix (Fin n) (Fin m) K)
    (hq : M.rank = q) (rows : Fin q → Fin n) (cols : Fin q → Fin m) :
    (M.submatrix rows cols).det ≠ 0 ↔
      LinearIndependent K (M.row ∘ rows) ∧ LinearIndependent K (M.col ∘ cols) := by
  let restrict := LinearMap.funLeft K K cols
  constructor
  · intro h
    exact ⟨LinearIndependent.of_comp restrict (Matrix.linearIndependent_rows_of_det_ne_zero h),
      LinearIndependent.of_comp (LinearMap.funLeft K K rows)
        (Matrix.linearIndependent_cols_of_det_ne_zero h)⟩
  · rintro ⟨hrows, hcols⟩
    -- The selected rows span the whole row space before restriction to the columns.
    have hspan : Submodule.span K (range (M.row ∘ rows)) = Submodule.span K (range M.row) := by
      apply Submodule.eq_of_le_of_finrank_eq
      · exact Submodule.span_mono (range_comp_subset_range ..)
      · rw [← M.rank_eq_finrank_span_row, hq]
        simpa [Set.finrank] using (linearIndependent_iff_card_eq_finrank_span.mp hrows).symm
    -- Restricting both equal spaces to the selected columns preserves equality.
    have hrank : (M.submatrix rows cols).rank = (M.submatrix id cols).rank := by
      rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
      have hs := congrArg (Submodule.map restrict) hspan
      rw [Submodule.map_span, Submodule.map_span, ← range_comp, ← range_comp] at hs
      exact congrArg (fun S : Submodule K (Fin q → K) => Module.finrank K S) hs
    have hfull : (M.submatrix rows cols).rank = Fintype.card (Fin q) := by
      rw [hrank, Matrix.rank_eq_finrank_span_cols]
      exact (linearIndependent_iff_card_eq_finrank_span.mp hcols).symm
    have h : LinearIndependent K (M.submatrix rows cols).row := by
      apply linearIndependent_iff_card_eq_finrank_span.mpr
      exact hfull.symm.trans (Matrix.rank_eq_finrank_span_row _)
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp h)).ne_zero

/-- At the rank of the matrix, the nonzero minors are precisely the pairs of
independent row and column selections. -/
theorem compound_ne_zero_iff (M : Matrix (Fin n) (Fin m) K) (hq : M.rank = q)
    (I : powersetCard (Fin n) q) (J : powersetCard (Fin m) q) :
    compound q M I J ≠ 0 ↔
      LinearIndependent K (fun i : I.val => M.row i.val) ∧
      LinearIndependent K (fun j : J.val => M.col j.val) := by
  rw [compound, det_submatrix_ne_zero_iff M hq]
  apply and_congr
  · exact linearIndependent_equiv (R := K) (f := fun i : I.val => M.row i.val)
      (orderIsoOfFin I).toEquiv
  · exact linearIndependent_equiv (R := K) (f := fun j : J.val => M.col j.val)
      (orderIsoOfFin J).toEquiv

/-- Every minor of order strictly greater than the matrix rank vanishes. -/
theorem compound_eq_zero_of_rank_lt (M : Matrix (Fin n) (Fin m) K) (hq : M.rank < q)
    (I : powersetCard (Fin n) q) (J : powersetCard (Fin m) q) : compound q M I J = 0 := by
  by_contra h
  let rows := ofFinEmbEquiv.symm I
  let cols := ofFinEmbEquiv.symm J
  have hrank : (M.submatrix rows cols).rank = Fintype.card (Fin q) :=
    (Matrix.linearIndependent_rows_of_det_ne_zero
    (show (M.submatrix rows cols).det ≠ 0 from h)).rank_matrix
  have hle := M.rank_submatrix_le rows cols
  rw [hrank, Fintype.card_fin] at hle
  exact hq.not_ge hle

end RankQuery

end VPVNP
end Computability
end OAI
