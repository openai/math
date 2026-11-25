import OAI.LinearAlgebra.SpectralBooks.IncrementMasks

/-! # Enumerating the sites in a one-site increment -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- Embed the coordinate format for an increment into the original site space.
The joint, old, auxiliary and full masks map to the four sets in the
diminishing-increments inequality. -/
theorem exists_incrementSite_embedding {X : Type*} [DecidableEq X]
    {I A : Finset X} (hI : I.Nonempty) (hIA : I ⊆ A) {z : X} (hz : z ∉ A) :
    ∃ e : IncrementSite (I.card - 1) (A \ I).card ↪ X,
      (incrementJointMask _ _).map e = I ∧ (incrementOldMask _ _).map e = A ∧
      (incrementAuxMask _ _).map e = insert z I ∧ Finset.univ.map e = insert z A := by
  have hcard : 0 < I.card := Finset.card_pos.mpr hI
  let i := (I.equivFinOfCardEq (show I.card = (I.card - 1) + 1 by omega)).symm
  let j := (A \ I).equivFin.symm
  let f : IncrementSite (I.card - 1) (A \ I).card → X
    | .inl k => i k
    | .inr none => z
    | .inr (some k) => j k
  have hInject : Function.Injective f := by
    have hi (k) := (i k).property
    have hj (k) := Finset.mem_sdiff.mp (j k).property
    rintro (a | _ | a) (b | _ | b) h <;> dsimp only [f] at h
    · exact congrArg Sum.inl (i.injective (Subtype.ext h))
    · exact (hz (h ▸ hIA (hi a))).elim
    · exact ((hj b).2 (h ▸ hi a)).elim
    · exact (hz (h.symm ▸ hIA (hi b))).elim
    · rfl
    · exact (hz (h.symm ▸ (hj b).1)).elim
    · exact ((hj a).2 (h.symm ▸ hi b)).elim
    · exact (hz (h ▸ (hj a).1)).elim
    · exact congrArg (fun k => Sum.inr (some k)) (j.injective (Subtype.ext h))
  let e : IncrementSite (I.card - 1) (A \ I).card ↪ X := ⟨f, hInject⟩
  have joint : (incrementJointMask _ _).map e = I := by
    ext x
    simp only [incrementJointMask, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.inl_apply, exists_exists_eq_and]
    constructor
    · rintro ⟨k, rfl⟩
      exact (i k).property
    · intro hx
      exact ⟨i.symm ⟨x,hx⟩, by change (i (i.symm _) : X) = x; simp⟩
  have old : (incrementOldMask _ _).map e = A := by
    ext x
    simp only [incrementOldMask, Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases k with k | _ | k
      · exact hIA (i k).property
      · exact (hk rfl).elim
      · exact (Finset.mem_sdiff.mp (j k).property).1
    · intro hx
      by_cases hin : x ∈ I
      · exact ⟨.inl (i.symm ⟨x,hin⟩), by simp, by change (i (i.symm _) : X) = x; simp⟩
      · have hj : x ∈ A \ I := Finset.mem_sdiff.mpr ⟨hx,hin⟩
        exact ⟨.inr (some (j.symm ⟨x,hj⟩)), by simp, by change (j (j.symm _) : X) = x; simp⟩
  have ez : e (.inr none) = z := rfl
  refine ⟨e, joint, old, ?_, ?_⟩
  · rw [incrementAuxMask, Finset.map_insert, ez, joint]
  · calc
      Finset.univ.map e = (insert (.inr none) (incrementOldMask _ _)).map e := by
        simp [incrementOldMask]
      _ = insert z A := by rw [Finset.map_insert, old, ez]

end SpectralBooks
end LinearAlgebra
end OAI
