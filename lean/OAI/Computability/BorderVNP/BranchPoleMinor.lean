import OAI.Computability.BorderVNP.BranchPoleBidegree
import OAI.Computability.VPVNP.SliceGeometryPencil

/-! # A bounded polynomial vanishing on finite rank jumps

The maximal minors of an augmented Macaulay matrix need not be recorded. We only use
one of them to find a maximal-rank specialization away from the finite zero fiber.
A minor of the original matrix at that specialization then vanishes at every point of
the fiber and has explicit bidegree bounds in the original coefficient field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open Polynomial VPVNP.Crossing VPVNP.RankQuery

private theorem exists_full_minor {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    (M : Matrix I J K) : ∃ (rows : Fin M.rank → I) (cols : Fin M.rank → J),
      (M.submatrix rows cols).det ≠ 0 := by
  classical
  let e := (Fintype.equivFin I).symm
  let f := (Fintype.equivFin J).symm
  let A := M.submatrix e f
  have hr : A.rank = M.rank := Matrix.rank_submatrix _ _ _
  obtain ⟨U, hu, _⟩ := exists_isolatedBasis K A.row (hr.symm.trans A.rank_eq_finrank_span_row)
  obtain ⟨V, hv, _⟩ := exists_isolatedBasis K A.col (hr.symm.trans A.rank_eq_finrank_span_cols)
  exact ⟨e ∘ Set.powersetCard.ofFinEmbEquiv.symm U, f ∘ Set.powersetCard.ofFinEmbEquiv.symm V,
    (compound_ne_zero_iff A hr U V).mpr ⟨hu, hv⟩⟩

private theorem rank_ge_of_minor {K I J : Type*} [Field K] [Fintype J]
    (M : Matrix I J K) {r : ℕ} (rows : Fin r → I) (cols : Fin r → J)
    (hn : (M.submatrix rows cols).det ≠ 0) : r ≤ M.rank := by
  have he := M.rank_submatrix_le rows cols
  rwa [Matrix.rank_of_det_ne_zero hn, Fintype.card_fin] at he

private theorem exists_max_rank_away {K I J : Type*} [Field K] [Infinite K] [Fintype I] [Fintype J]
    (M : Matrix I J (Polynomial K)) (S : Set K) (hS : S.Finite) :
    ∃ a ∉ S, ∀ b, (M.map (Polynomial.eval b)).rank ≤ (M.map (Polynomial.eval a)).rank := by
  classical
  let ρ (a : K) := (M.map (Polynomial.eval a)).rank
  have hb : BddAbove (Set.range ρ) :=
    ⟨Fintype.card J, fun _ ⟨a, ha⟩ ↦ ha ▸ (M.map (Polynomial.eval a)).rank_le_card_width⟩
  obtain ⟨a₀, ha₀⟩ := Nat.sSup_mem (Set.range_nonempty ρ) hb
  have hmax (b : K) : ρ b ≤ ρ a₀ := ha₀ ▸ le_csSup hb (Set.mem_range_self b)
  obtain ⟨rows, cols, hn⟩ := exists_full_minor (M.map (Polynomial.eval a₀))
  let D := (M.submatrix rows cols).det
  have he (a : K) : D.eval a = ((M.map (Polynomial.eval a)).submatrix rows cols).det :=
    (Polynomial.evalRingHom a).map_det _
  have hD : D ≠ 0 := by
    intro hz
    apply hn
    rw [← he, hz, Polynomial.eval_zero]
  have hfin := hS.union (Polynomial.finite_setOfPred_isRoot hD)
  obtain ⟨a, ha⟩ := hfin.exists_notMem
  have has : a ∉ S := fun h ↦ ha (Or.inl h)
  have hd : D.eval a ≠ 0 := fun h ↦ ha (Or.inr h)
  refine ⟨a, has, fun b ↦ (hmax b).trans ?_⟩
  exact rank_ge_of_minor _ rows cols ((he a) ▸ hd)

/-- A finite strict rank-jump locus over the generic coefficient field is annihilated by
a nonzero determinant in the original parameter and value indeterminates. -/
theorem rank_jump_eliminant {K L I I' J : Type*} [Field K] [Field L] [Infinite L]
    [Fintype I] [Fintype I'] [Fintype J] (φ : Polynomial K →+* L)
    (M : Matrix I J (Polynomial (Polynomial K))) (N : Matrix I' J (Polynomial (Polynomial K)))
    {e : ℕ} (hw : ∀ i j, (M i j).natDegree ≤ 1)
    (ht : ∀ i j k, ((M i j).coeff k).natDegree ≤ e)
    (hfin : {a : L | (M.map (Polynomial.eval₂RingHom φ a)).rank <
      (N.map (Polynomial.eval₂RingHom φ a)).rank}.Finite) :
    ∃ D : Polynomial (Polynomial K), D ≠ 0 ∧ D.natDegree ≤ Fintype.card J ∧
      (∀ k, (D.coeff k).natDegree ≤ Fintype.card J * e) ∧
      ∀ a : L, (M.map (Polynomial.eval₂RingHom φ a)).rank <
        (N.map (Polynomial.eval₂RingHom φ a)).rank → D.eval₂ φ a = 0 := by
  classical
  let S := {a : L | (M.map (Polynomial.eval₂RingHom φ a)).rank <
    (N.map (Polynomial.eval₂RingHom φ a)).rank}
  let N' := N.map (Polynomial.map φ)
  have hN (a : L) : N'.map (Polynomial.eval a) = N.map (Polynomial.eval₂RingHom φ a) := by
    ext i j
    exact Polynomial.eval_map φ a
  obtain ⟨a, ha, hmax⟩ := exists_max_rank_away N' S hfin
  simp_rw [hN] at hmax
  let A := M.map (Polynomial.eval₂RingHom φ a)
  obtain ⟨rows, cols, hn⟩ := exists_full_minor A
  let T := M.submatrix rows cols
  let D := T.det
  have he (w : L) : D.eval₂ φ w =
      ((M.map (Polynomial.eval₂RingHom φ w)).submatrix rows cols).det :=
    (Polynomial.eval₂RingHom φ w).map_det _
  have hD : D ≠ 0 := by
    intro hz
    apply hn
    rw [← he, hz, Polynomial.eval₂_zero]
  refine ⟨D, hD, ?_, ?_, ?_⟩
  · exact (natDegree_det_le T (fun i j ↦ hw (rows i) (cols j))).trans
      (by simpa using A.rank_le_card_width)
  · exact fun k ↦ (coeff_natDegree_det_le T (fun i j ↦ ht (rows i) (cols j)) k).trans
      (Nat.mul_le_mul_right _ A.rank_le_card_width)
  · intro w hw'
    by_contra hn'
    have hle := rank_ge_of_minor (M.map (Polynomial.eval₂RingHom φ w)) rows cols ((he w) ▸ hn')
    exact ha (lt_of_le_of_lt hle (hw'.trans_le (hmax w)))

end Branch

end BorderVNP
end Computability
end OAI
