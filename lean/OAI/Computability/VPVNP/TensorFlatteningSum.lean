import OAI.Computability.VPVNP.TensorFlattening
import OAI.Computability.VPVNP.TensorDistributivity
import OAI.Computability.VPVNP.FlatteningBlockRank

/-!
# Direct sums in one-party flattenings

Across a nontrivial cut, the pure columns form the block diagonal matrix of
the two summands. A column using both summands on the complementary parties
vanishes, so the full flattening and the block matrix have the same column span.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

variable {k J : Type*} [Field k] [Fintype J] [DecidableEq J] [Nontrivial J]

omit [Fintype J] [Nontrivial J] in
private theorem joinBasis_map {B C : J → Type*} (f : ∀ j, B j → C j)
    (a : J) (x : B a) (y : OtherBasis a B) :
    joinBasis a (f a x) (fun j ↦ f j (y j)) = fun j ↦ f j (joinBasis a x y j) := by
  funext j
  by_cases hj : j = a
  · subst j
    simp
  · exact (joinBasis_other a _ _ ⟨j, hj⟩).trans
      (congrArg (f j) (joinBasis_other a x y ⟨j, hj⟩)).symm

private theorem flattening_directSum_pureColumn (a : J) (T U : Tensor k J)
    (y : OtherBasis a T.Basis ⊕ OtherBasis a U.Basis) :
    (flattening a (directSum T U)).col
        (y.elim (fun l j ↦ Sum.inl (l j)) (fun r j ↦ Sum.inr (r j))) =
      (Matrix.fromBlocks (flattening a T) 0 0 (flattening a U)).col y := by
  obtain ⟨b, hb⟩ := exists_ne a
  funext x
  rcases x with l | r <;> rcases y with l' | r'
  · change (directSum T U).coeff (joinBasis a (.inl l) (fun j ↦ .inl (l' j))) = _
    exact (congrArg (directSum T U).coeff (joinBasis_map (C := (directSum T U).Basis)
      (fun _ ↦ Sum.inl) a l l')).trans (directSum_coeff_inl T U _)
  · apply directSum_coeff_mixed T U _ (a := a) (b := b) (i := l) (l := r' ⟨b, hb⟩)
    · exact joinBasis_self a _ _
    · exact joinBasis_other a _ _ ⟨b, hb⟩
  · apply directSum_coeff_mixed T U _ (a := b) (b := a) (i := l' ⟨b, hb⟩) (l := r)
    · exact joinBasis_other a _ _ ⟨b, hb⟩
    · exact joinBasis_self a _ _
  · change (directSum T U).coeff (joinBasis a (.inr r) (fun j ↦ .inr (r' j))) = _
    exact (congrArg (directSum T U).coeff (joinBasis_map (C := (directSum T U).Basis)
      (fun _ ↦ Sum.inr) a r r')).trans (directSum_coeff_inr T U _)

/-- Mixed columns are zero, so deleting them from the direct-sum flattening
preserves its rank. -/
theorem flattening_directSum_rank_block (a : J) (T U : Tensor k J) :
    (flattening a (directSum T U)).rank =
      (Matrix.fromBlocks (flattening a T) 0 0 (flattening a U)).rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  apply congrArg (fun p : Submodule k ((T.Basis a ⊕ U.Basis a) → k) ↦ Module.finrank k p)
  apply le_antisymm <;> apply Submodule.span_le.mpr <;> rintro _ ⟨y, rfl⟩
  · rcases sum_assignment_cases (A := fun j : {j : J // j ≠ a} ↦ T.Basis j)
        (B := fun j ↦ U.Basis j) y with ⟨l, rfl⟩ | ⟨r, rfl⟩ | ⟨i, j, l, r, hi, hj⟩
    · exact Submodule.subset_span (R := k) (M := (T.Basis a ⊕ U.Basis a) → k)
        ⟨.inl l, (flattening_directSum_pureColumn a T U (.inl l)).symm⟩
    · exact Submodule.subset_span (R := k) (M := (T.Basis a ⊕ U.Basis a) → k)
        ⟨.inr r, (flattening_directSum_pureColumn a T U (.inr r)).symm⟩
    · have hz : (flattening a (directSum T U)).col y = 0 := by
        funext x
        apply directSum_coeff_mixed T U _ (a := i.1) (b := j.1) (i := l) (l := r)
        · exact (joinBasis_other a x y i).trans hi
        · exact (joinBasis_other a x y j).trans hj
      rw [hz]
      exact Submodule.zero_mem _
  · exact Submodule.subset_span (R := k) (M := (directSum T U).Basis a → k)
      ⟨_, flattening_directSum_pureColumn a T U y⟩

/-- Flattening rank is additive under direct sum when there are at least two parties. -/
theorem flattening_directSum_rank (a : J) (T U : Tensor k J) :
    (flattening a (directSum T U)).rank = (flattening a T).rank + (flattening a U).rank :=
  (flattening_directSum_rank_block a T U).trans (rank_fromBlocks_zero _ _)

end WireTensor

end VPVNP
end Computability
end OAI
