import OAI.Computability.NearSquareRoot.SynchronizedPlacementAddress
import OAI.Computability.NearSquareRoot.SynchronizedFiberWord

/-! # Tables on physical cells of a borrowing batch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedBorrowing
noncomputable section
variable {a b c r : ℕ}

/-- Include the allocated coordinates in the full padded physical block. -/
def fullBatchCells (hr : 2*r ≤ 8*a) (j : Fin 15) :
    (Fin a ⊕ Fin (2*r-a)) × Fin (size b j) ↪ Fin b × (Fin a ⊕ Fin c) :=
  (Equiv.prodComm ..).toEmbedding.trans ((batchPlacement b j hr).trans
    ((Function.Embedding.refl _).prodMap Function.Embedding.inl))

/-- Rank within the physical axis includes padding at the end of each row. -/
def cellLookup (r : ℕ) (j : Fin 15) (p : Fin b × (Fin a ⊕ Fin c)) : Option (ℕ × ℕ) :=
  let col := (finSumFinEquiv p.2).val
  if col < a then lookupRank (first b j) (size b j) a r (p.1.val*a+col) else none

theorem cellLookup_placed (ha : 0 < a) (har : a ≤ r) (hr : 2*r ≤ 8*a) (j : Fin 15)
    (q : (Fin a ⊕ Fin (2*r-a)) × Fin (size b j)) :
    cellLookup r j (fullBatchCells (c := c) hr j q) = some (q.2.val,(finSumFinEquiv q.1).val) := by
  let t := batchPlacement b j hr (q.2,q.1)
  change (if (finSumFinEquiv (.inl t.2 : Fin a ⊕ Fin c)).val < a then
    lookupRank (first b j) (size b j) a r (t.1.val*a+(finSumFinEquiv (.inl t.2 : Fin a ⊕ Fin c)).val)
      else none) = _
  change (if t.2.val < a then lookupRank (first b j) (size b j) a r (t.1.val*a+t.2.val) else none) = _
  simp only [t.2.isLt, ite_true]
  have hval : t.1.val*a+t.2.val = (finProdFinEquiv t).val := by change _ = t.2.val+a*t.1.val; ring
  have hflat := (finSumFinEquiv q.1).isLt
  rw [hval]
  exact (congrArg (lookupRank (first b j) (size b j) a r) (placement_rank (batchFits b j)
    (show size b j ≤ b/8 from min_le_left _ _) hr q.2 q.1)).trans
      (lookup_physicalRank ha har q.2.isLt (by omega))

theorem cellLookup_eq_none_iff (ha : 0 < a) (har : a ≤ r) (hr : 2*r ≤ 8*a) (j : Fin 15)
    (p : Fin b × (Fin a ⊕ Fin c)) :
    cellLookup r j p = none ↔ p ∉ Set.range (fullBatchCells hr j) := by
  constructor
  · rintro hn ⟨q,rfl⟩
    rw [cellLookup_placed ha har] at hn
    contradiction
  · intro hn
    by_contra h
    obtain ⟨⟨i,u⟩,hu⟩ := Option.ne_none_iff_exists'.mp h
    rcases p with ⟨row,col|pad⟩
    · have hq : lookupRank (first b j) (size b j) a r (row.val*a+col.val) = some (i,u) := by
        simpa [cellLookup, col.isLt] using hu
      obtain ⟨hi,hf,hval⟩ := (lookupRank_iff ha har).mp hq
      let t : Fin a ⊕ Fin (2*r-a) := finSumFinEquiv.symm ⟨u,by omega⟩
      let q : (Fin a ⊕ Fin (2*r-a)) × Fin (size b j) := (t,⟨i,hi⟩)
      apply hn
      refine ⟨q,?_⟩
      have hit : batchPlacement b j hr (q.2,q.1) = (row,col) := by
        apply finProdFinEquiv.injective
        apply Fin.ext
        calc
          _ = physicalRank (first b j) (size b j) a r q.2.val (finSumFinEquiv q.1).val :=
            placement_rank (batchFits b j) (show size b j ≤ b/8 from min_le_left _ _) hr q.2 q.1
          _ = physicalRank (first b j) (size b j) a r i u := by simp [q,t]
          _ = _ := hval.trans (by change row.val*a+col.val = col.val+a*row.val; ring)
      exact congrArg (fun q : Fin b × Fin a => (q.1,Sum.inl q.2)) hit
    · simp [cellLookup] at hu

/-- The phase at each physical cell is one unless the inverse address table
finds a local entry. -/
def placedPhase (r : ℕ) (j : Fin 15) (d : ℕ → ℂ) (p : Fin b × (Fin a ⊕ Fin c)) : ℂ :=
  ((cellLookup r j p).map (fun z => d z.2)).getD 1

theorem placedPhase_diagonal (ha : 0 < a) (har : a ≤ r) (hr : 2*r ≤ 8*a) (j : Fin 15)
    (d : ℕ → ℂ) :
    batchMatrix (b := b) (c := c) hr j (diagonal (fun t => d (finSumFinEquiv t).val)) =
      diagonal (placedPhase r j d) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  change placeHom (fullBatchCells hr j) _ *ᵥ x = _
  rw [placeHom_mulVec]
  funext p
  by_cases h : p ∈ Set.range (fullBatchCells hr j)
  · obtain ⟨q,rfl⟩ := h
    rw [(fullBatchCells hr j).injective.extend_apply]
    simp [mulVec_diagonal, placedPhase, cellLookup_placed ha har]
  · rw [Function.extend_apply' _ _ _ h]
    simp [mulVec_diagonal, placedPhase, (cellLookup_eq_none_iff ha har hr j p).mpr h]

end
end ShortFourier

end NearSquareRoot
end Computability
end OAI
