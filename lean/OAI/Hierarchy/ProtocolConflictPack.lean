import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace OAI
/-! # Sequential packing of the failing balls of a protocol

Visit candidate roots in ordinal order. A failing root is selected exactly
when its bounded list of neighbours contains no earlier selection. Padding
with the row's own address does not change this decision.
-/

namespace Hierarchy.ProtocolConflictPack
open scoped Classical
variable {n d : ℕ}

/-- The decision only inspects selected bits at strictly smaller row ordinals. -/
def Chosen (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n) (v : Fin n) : Prop :=
  fail v = true ∧ ∀ j, (adj v j).val < v.val → ¬ Chosen fail adj (adj v j)
termination_by v.val
decreasing_by assumption

theorem chosen_iff (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n) (v : Fin n) :
    Chosen fail adj v ↔ fail v = true ∧ ∀ j, adj v j < v → ¬Chosen fail adj (adj v j) := by
  rw [Chosen]
  simp only [Fin.lt_def]

noncomputable def picked (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n) :=
  Finset.univ.filter (Chosen fail adj)

theorem independent (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n)
    (symm : ∀ v j, ∃ l, adj (adj v j) l = v) {v : Fin n} (hv : Chosen fail adj v)
    (j : Fin d) (different : adj v j ≠ v) : ¬Chosen fail adj (adj v j) := by
  intro hit
  rcases lt_or_gt_of_ne different with low | high
  · exact ((chosen_iff ..).mp hv).2 j low hit
  · obtain ⟨l,hl⟩ := symm v j
    have earlier := ((chosen_iff ..).mp hit).2 l
    rw [hl] at earlier
    exact earlier high hv

/-- When the conflict lists include every pair sharing a tile, the native
selection has disjoint tile sets, even if rows or list entries were padded. -/
theorem disjoint_picked {α : Type*} (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n)
    (tiles : Fin n → Finset α) (symm : ∀ v j, ∃ l, adj (adj v j) l = v)
    (listed : ∀ u v,u≠v → ¬Disjoint (tiles u) (tiles v) → ∃ j,adj u j=v)
    {u v : Fin n} (hu : Chosen fail adj u) (hv : Chosen fail adj v) (ne : u≠v) :
    Disjoint (tiles u) (tiles v) := by
  by_contra overlap
  obtain ⟨j,hit⟩ := listed u v ne overlap
  have misses := independent fail adj symm hu j (by simpa [hit] using ne.symm)
  rw [hit] at misses
  exact misses hv

theorem dominates (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n)
    {v : Fin n} (failing : fail v = true) :
    Chosen fail adj v ∨ ∃ j, adj v j < v ∧ Chosen fail adj (adj v j) := by
  by_cases hit : Chosen fail adj v
  · exact Or.inl hit
  right
  by_contra no
  exact hit ((chosen_iff fail adj v).2 ⟨failing,fun j h picked => no ⟨j,h,picked⟩⟩)

/-- At most one root and its listed neighbours can be charged to each pick. -/
theorem density (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n)
    (symm : ∀ v j, ∃ l, adj (adj v j) l = v) :
    (Finset.univ.filter (fun v => fail v=true)).card ≤ (picked fail adj).card*(d+1) := by
  classical
  let closed (v : Fin n) := insert v (Finset.univ.image (adj v))
  have cover : Finset.univ.filter (fun v => fail v=true) ⊆ (picked fail adj).biUnion closed := by
    intro v hv
    rcases dominates fail adj (Finset.mem_filter.mp hv).2 with hit | ⟨j,_,hit⟩
    · exact Finset.mem_biUnion.mpr ⟨v,by simpa [picked] using hit,Finset.mem_insert_self ..⟩
    · obtain ⟨l,hl⟩ := symm v j
      exact Finset.mem_biUnion.mpr ⟨adj v j, by simpa [picked] using hit,
        Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨l,Finset.mem_univ _,hl⟩)⟩
  apply (Finset.card_le_card cover).trans (Finset.card_biUnion_le_card_mul _ _ _ ?_)
  intro v _
  exact (Finset.card_insert_le ..).trans (Nat.add_le_add_right
    (by simpa using (Finset.card_image_le (s:=Finset.univ) (f:=adj v))) 1)

end Hierarchy.ProtocolConflictPack

end OAI
