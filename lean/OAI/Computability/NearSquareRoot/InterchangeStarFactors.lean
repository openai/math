import OAI.Computability.NearSquareRoot.InterchangeStar

/-! # Gaussian elimination by batches of transvections

At most three new batches clear the last row and column. The batches on the
smaller matrix are then embedded in the remaining block. Counts are the numbers
of batches, independently of the number of transvections inside each batch.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open Matrix Matrix.TransvectionStruct

private abbrev Batches (I : Type*) := List (List (TransvectionStruct I ℚ))

private def HasReduction {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℚ) (budget : ℕ) : Prop :=
  ∃ (L R : Batches I) (D : I → ℚ),
    (∀ s ∈ L, IsStar s) ∧ (∀ s ∈ R, IsStar s) ∧ L.length + R.length ≤ budget ∧
    (L.flatten.map toMatrix).prod * M * (R.flatten.map toMatrix).prod = diagonal D

private theorem star_map {I J : Type*} {s : List (TransvectionStruct I ℚ)} (h : IsStar s)
    (f : TransvectionStruct I ℚ → TransvectionStruct J ℚ) (g : I → J)
    (hi : ∀ x, (f x).i = g x.i) (hj : ∀ x, (f x).j = g x.j) : IsStar (s.map f) := by
  obtain ⟨i, hi'⟩ | ⟨i, hj'⟩ := h
  · left
    refine ⟨g i, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [hi, hi' y hy]
  · right
    refine ⟨g i, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [hj, hj' y hy]

private theorem stars_map {I J : Type*} {L : Batches I} (h : ∀ s ∈ L, IsStar s)
    (f : TransvectionStruct I ℚ → TransvectionStruct J ℚ) (g : I → J)
    (hi : ∀ x, (f x).i = g x.i) (hj : ∀ x, (f x).j = g x.j) :
    ∀ s ∈ L.map (List.map f), IsStar s := by
  intro s hs
  obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
  exact star_map (h s₀ hs₀) f g hi hj

private theorem lift_reduction {r : ℕ}
    (ih : ∀ M : Matrix (Fin r) (Fin r) ℚ, HasReduction M (3*r))
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) ℚ) : HasReduction M (3*(r+1)) := by
  obtain ⟨L, R, hl, hr, hc, hd⟩ := pivot_stars M
  let N := (L.flatten.map toMatrix).prod * M * (R.flatten.map toMatrix).prod
  obtain ⟨L₀, R₀, D, hl₀, hr₀, hc₀, hD⟩ := ih (toBlocks₁₁ N)
  let c := N (.inr ()) (.inr ())
  let lift := List.map (sumInl Unit : TransvectionStruct (Fin r) ℚ → _)
  refine ⟨L₀.map lift ++ L, R ++ R₀.map lift, Sum.elim D (fun _ => c), ?_, ?_, ?_, ?_⟩
  · exact fun s hs => (List.mem_append.mp hs).elim
      (stars_map hl₀ _ Sum.inl (fun _ => rfl) (fun _ => rfl) _) (hl _)
  · exact fun s hs => (List.mem_append.mp hs).elim (hr _)
      (stars_map hr₀ _ Sum.inl (fun _ => rfl) (fun _ => rfl) _)
  · simp only [List.length_append, List.length_map]
    omega
  · suffices (L₀.flatten.map (toMatrix ∘ sumInl Unit)).prod * N *
          (R₀.flatten.map (toMatrix ∘ sumInl Unit)).prod = diagonal (Sum.elim D fun _ => c) by
      simpa only [lift, List.flatten_append, ← List.map_flatten, List.map_append,
        List.map_map, List.prod_append, N, Matrix.mul_assoc] using this
    have hblocks : N = fromBlocks (toBlocks₁₁ N) 0 0 (diagonal fun _ => c) := by
      conv_lhs => rw [← fromBlocks_toBlocks N]
      rw [show toBlocks₁₂ N = 0 from hd.1, show toBlocks₂₁ N = 0 from hd.2]
      rfl
    calc
      _ = fromBlocks ((L₀.flatten.map toMatrix).prod * toBlocks₁₁ N *
          (R₀.flatten.map toMatrix).prod) 0 0 (diagonal fun _ => c) := by
        conv_lhs => rw [hblocks]
        rw [sumInl_toMatrix_prod_mul, mul_sumInl_toMatrix_prod]
      _ = _ := by rw [hD]; simp

private theorem reindex_reduction {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (M : Matrix I I ℚ) (e : I ≃ J) {k : ℕ}
    (h : HasReduction (reindexAlgEquiv ℚ _ e M) k) : HasReduction M k := by
  obtain ⟨L, R, D, hl, hr, hc, hd⟩ := h
  let pull := List.map (reindexEquiv e.symm : TransvectionStruct J ℚ → _)
  refine ⟨L.map pull, R.map pull, D ∘ e, ?_, ?_, by simpa only [List.length_map] using hc, ?_⟩
  · exact stars_map hl _ e.symm (fun _ => rfl) (fun _ => rfl)
  · exact stars_map hr _ e.symm (fun _ => rfl) (fun _ => rfl)
  · have he : M = reindexAlgEquiv ℚ _ e.symm (reindexAlgEquiv ℚ _ e M) := by simp
    rw [he]
    simp_rw [pull, ← List.map_flatten, List.map_map, toMatrix_reindexEquiv_prod, ← map_mul, hd]
    simp

private theorem finite_reduction (r : ℕ) (M : Matrix (Fin r) (Fin r) ℚ) :
    HasReduction M (3*r) := by
  induction r with
  | zero => exact ⟨[], [], fun _ => 1, by simp, by simp, by simp, Subsingleton.elim _ _⟩
  | succ r ih =>
    let e : Fin (r+1) ≃ Fin r ⊕ Unit := Fintype.equivOfCardEq (by simp)
    exact reindex_reduction M e (lift_reduction ih _)

/-- On a matrix with `d` field indices, at most `3*d` common-source or
common-target batches and one pointwise diagonal suffice for elimination. -/
theorem diagonalize_stars {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℚ) :
    ∃ (L R : List (List (TransvectionStruct I ℚ))) (D : I → ℚ),
      (∀ s ∈ L, IsStar s) ∧ (∀ s ∈ R, IsStar s) ∧
      L.length + R.length ≤ 3 * Fintype.card I ∧
      (L.flatten.map toMatrix).prod * M * (R.flatten.map toMatrix).prod = diagonal D :=
  reindex_reduction M (Fintype.equivFin I) (finite_reduction _ _)

end Interchange

end NearSquareRoot
end Computability
end OAI
