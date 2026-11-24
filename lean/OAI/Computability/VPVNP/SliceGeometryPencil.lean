import OAI.Computability.VPVNP.GreedyBasis
import OAI.Computability.VPVNP.RankMinors
import OAI.Computability.VPVNP.SliceGeometryPinning
import Mathlib.Algebra.Polynomial.Roots

/-!
# Exceptional parameters for matrices of affine polynomials

A maximal-rank specialization supplies a nonzero minor. Its determinant
remains nonzero off at most one exceptional scalar per column, because the
matrix entries have degree at most one. Comparing two such ranks therefore
gives a bounded or cobounded parameter set.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceGeometry

open VPVNP.Crossing VPVNP.RankQuery
open scoped Polynomial

variable {E : Type*} [Field E]

private theorem natDegree_det_le_card {q : ℕ} (M : Matrix (Fin q) (Fin q) E[X])
    (hd : ∀ i j, (M i j).natDegree ≤ 1) : M.det.natDegree ≤ q := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  apply (Polynomial.natDegree_smul_le _ _).trans
  calc
    _ ≤ ∑ i, (M (σ i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _ : Fin q, 1 := Finset.sum_le_sum (fun i _ => hd (σ i) i)
    _ = _ := by simp

/-- The rank is constant away from at most `#J` parameters. This also covers
empty matrices and finite fields. -/
theorem exists_generic_rank {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J E[X]) (hd : ∀ i j, (M i j).natDegree ≤ 1) :
    ∃ (r : ℕ) (S : Finset E), S.card ≤ Fintype.card J ∧
      ∀ c ∉ S, (M.map (Polynomial.eval c)).rank = r := by
  classical
  let ρ (c : E) := (M.map (Polynomial.eval c)).rank
  have hb : BddAbove (Set.range ρ) :=
    ⟨Fintype.card J, fun _ ⟨c, h⟩ => h ▸ (M.map (Polynomial.eval c)).rank_le_card_width⟩
  obtain ⟨c₀, hc⟩ := Nat.sSup_mem (Set.range_nonempty ρ) hb
  have hmax (c : E) : ρ c ≤ ρ c₀ := hc ▸ le_csSup hb (Set.mem_range_self c)
  let e := (Fintype.equivFin I).symm
  let f := (Fintype.equivFin J).symm
  let A := (M.map (Polynomial.eval c₀)).submatrix e f
  have hr : A.rank = ρ c₀ := Matrix.rank_submatrix _ _ _
  obtain ⟨U, hu, _⟩ := exists_isolatedBasis E A.row (hr.symm.trans A.rank_eq_finrank_span_row)
  obtain ⟨V, hv, _⟩ := exists_isolatedBasis E A.col (hr.symm.trans A.rank_eq_finrank_span_cols)
  have hn := (compound_ne_zero_iff A hr U V).mpr ⟨hu, hv⟩
  let rows := e ∘ Set.powersetCard.ofFinEmbEquiv.symm U
  let cols := f ∘ Set.powersetCard.ofFinEmbEquiv.symm V
  let N := M.submatrix rows cols
  let D := N.det
  have he (c : E) : D.eval c = ((M.map (Polynomial.eval c)).submatrix rows cols).det :=
    (Polynomial.evalRingHom c).map_det N
  have hD : D ≠ 0 := by
    intro h0
    apply hn
    change ((M.map (Polynomial.eval c₀)).submatrix rows cols).det = 0
    rw [← he, h0, Polynomial.eval_zero]
  refine ⟨ρ c₀, D.roots.toFinset, (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' D).trans
    ((natDegree_det_le_card N (fun i j => hd (rows i) (cols j))).trans
      (M.map (Polynomial.eval c₀)).rank_le_card_width)), fun c h => ?_⟩
  apply le_antisymm (hmax c)
  have hdet : ((M.map (Polynomial.eval c)).submatrix rows cols).det ≠ 0 := by
    rw [← he]
    exact fun hz => h (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hD).mpr hz))
  have hle := (M.map (Polynomial.eval c)).rank_submatrix_le rows cols
  rwa [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hle

/-- The strict rank comparison of two affine polynomial matrices with the same
column type holds at finitely many parameters or at all but finitely many. -/
theorem boundedOrCobounded_rank_lt {I L J : Type*} [Fintype I] [Fintype L] [Fintype J]
    (M : Matrix I J E[X]) (N : Matrix L J E[X])
    (hm : ∀ i j, (M i j).natDegree ≤ 1) (hn : ∀ i j, (N i j).natDegree ≤ 1) :
    boundedOrCobounded {c : E | (M.map (Polynomial.eval c)).rank < (N.map (Polynomial.eval c)).rank}
      (2 * Fintype.card J) := by
  classical
  obtain ⟨r, S, hs, hr⟩ := exists_generic_rank M hm
  obtain ⟨q, T, ht, hq⟩ := exists_generic_rank N hn
  let U := S ∪ T
  have hU : (U : Set E).ncard ≤ 2 * Fintype.card J := by
    rw [Set.ncard_coe_finset, two_mul]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add hs ht)
  have hcmp (c : E) (hc : c ∉ U) :
      (M.map (Polynomial.eval c)).rank < (N.map (Polynomial.eval c)).rank ↔ r < q := by
    rw [hr c (fun h => hc (Finset.mem_union_left _ h)), hq c (fun h => hc (Finset.mem_union_right _ h))]
  by_cases hlt : r < q
  · right
    have hsub : {c : E | (M.map (Polynomial.eval c)).rank < (N.map (Polynomial.eval c)).rank}ᶜ ⊆ U := by
      intro c hc
      by_contra h
      exact hc ((hcmp c h).mpr hlt)
    exact ⟨U.finite_toSet.subset hsub, (Set.ncard_le_ncard hsub).trans hU⟩
  · left
    have hsub : {c : E | (M.map (Polynomial.eval c)).rank < (N.map (Polynomial.eval c)).rank} ⊆ U := by
      intro c hc
      by_contra h
      exact hlt ((hcmp c h).mp hc)
    exact ⟨U.finite_toSet.subset hsub, (Set.ncard_le_ncard hsub).trans hU⟩

end SliceGeometry

end VPVNP
end Computability
end OAI
