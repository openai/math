import OAI.Computability.VPVNP.ParseEvents

/-! # Local incidence validity of an ordered parse tree

Each non-root occurrence is requested by its parent, and each binary occurrence
requests exactly the roots of its two ordered subtrees. Their disjoint leaf
intervals give uniqueness at every occupied interval.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar.OrderedParse

variable {V H : Type*}

private theorem node_unique [DecidableEq V] [DecidableEq H] {r : ParseEvent V H}
    {L R : Finset (ParseEvent V H)} {l d b : ℕ} {i j : H}
    (hl : IsParseTable L l b i) (hr : IsParseTable R (l + b + 1) (d - b) j)
    (hrl : r.layer = d + 1) (hb : b ≤ d)
    (boundsL : ∀ e ∈ L, e.start + e.layer ≤ l + b ∧ e.layer ≤ b)
    (boundsR : ∀ e ∈ R, l + b + 1 ≤ e.start ∧ e.layer ≤ d - b) :
    ∀ e ∈ insert r (L ∪ R), ∀ f ∈ insert r (L ∪ R),
      e.start = f.start → e.layer = f.layer → e = f := by
  intro e he f hf hs hd
  simp only [Finset.mem_insert, Finset.mem_union] at he hf
  rcases he with rfl | he | he <;> rcases hf with rfl | hf | hf
  · rfl
  · have := (boundsL f hf).2
    omega
  · have := (boundsR f hf).2
    omega
  · have := (boundsL e he).2
    omega
  · exact hl.unique e he f hf hs hd
  · have := (boundsL e he).1
    have := (boundsR f hf).1
    omega
  · have := (boundsR e he).2
    omega
  · have := (boundsR e he).1
    have := (boundsL f hf).1
    omega
  · exact hr.unique e he f hf hs hd

private theorem table_node {V H : Type*} [DecidableEq V] [DecidableEq H]
    {L R : Finset (ParseEvent V H)} {l d b : ℕ} {h i j : H}
    (hb : b ≤ d) (hl : IsParseTable L l b i) (hr : IsParseTable R (l + b + 1) (d - b) j)
    (boundsL : ∀ e ∈ L, e.start + e.layer ≤ l + b ∧ e.layer ≤ b)
    (boundsR : ∀ e ∈ R, l + b + 1 ≤ e.start ∧ e.layer ≤ d - b) :
    IsParseTable (insert ⟨l, d + 1, h, .inr (b, i, j)⟩ (L ∪ R)) l (d + 1) h := by
  let r : ParseEvent V H := ⟨l, d + 1, h, .inr (b, i, j)⟩
  let T := insert r (L ∪ R)
  have rootMem : r ∈ T := Finset.mem_insert_self _ _
  have leftSub : L ⊆ T := fun _ he => Finset.mem_insert_of_mem (Finset.mem_union_left _ he)
  have rightSub : R ⊆ T := fun _ he => Finset.mem_insert_of_mem (Finset.mem_union_right _ he)
  have splitMem (e : ParseEvent V H) (he : e ∈ T) : e = r ∨ e ∈ L ∨ e ∈ R := by
    simpa only [T, Finset.mem_insert, Finset.mem_union] using he
  have req (x k : ℕ) (a : H) : r.Requests x k a ↔
      (x = l ∧ k = b ∧ a = i) ∨ (x = l + b + 1 ∧ k = d - b ∧ a = j) := by
    simp only [r, ParseEvent.Requests, show d + 1 - b - 1 = d - b by omega]
  refine ⟨⟨r, rootMem, ⟨rfl, rfl, rfl⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases splitMem e he with rfl | he | he
    · exact Nat.lt_succ_of_le hb
    · exact hl.typed e he
    · exact hr.typed e he
  · exact node_unique hl hr rfl hb boundsL boundsR
  · intro e he x k a ha
    rcases splitMem e he with rfl | he | he
    · rcases (req x k a).mp ha with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · obtain ⟨f, hf, hm⟩ := hl.root
        exact ⟨f, leftSub hf, hm⟩
      · obtain ⟨f, hf, hm⟩ := hr.root
        exact ⟨f, rightSub hf, hm⟩
    · obtain ⟨f, hf, hm⟩ := hl.children e he x k a ha
      exact ⟨f, leftSub hf, hm⟩
    · obtain ⟨f, hf, hm⟩ := hr.children e he x k a ha
      exact ⟨f, rightSub hf, hm⟩
  · intro e he
    rcases splitMem e he with rfl | he | he
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · right
      rcases hl.parent e he with hm | ⟨f, hf, hm⟩
      · exact ⟨r, rootMem, (req _ _ _).mpr (Or.inl hm)⟩
      · exact ⟨f, leftSub hf, hm⟩
    · right
      rcases hr.parent e he with hm | ⟨f, hf, hm⟩
      · exact ⟨r, rootMem, (req _ _ _).mpr (Or.inr hm)⟩
      · exact ⟨f, rightSub hf, hm⟩

/-- The interval occurrences of an ordered parse satisfy all local table conditions. -/
theorem events_isParseTable {V H : Type*} {d : ℕ} (t : OrderedParse V H d) (l : ℕ) (h : H) :
    IsParseTable (t.events l h) l d h := by
  classical
  induction t generalizing l h with
  | leaf v =>
    let r := (leaf v : OrderedParse V H 0).rootEvent l h
    have mem {e : ParseEvent V H} (he : e ∈ (leaf v).events l h) : e = r := by
      simpa only [events, Finset.mem_singleton] using he
    refine ⟨⟨r, rootEvent_mem _ _ _, rootEvent_matches _ _ _⟩, ?_, ?_, ?_, ?_⟩
    · intro e he
      rw [mem he]
      rfl
    · intro e he f hf _ _
      exact (mem he).trans (mem hf).symm
    · intro e he x k a ha
      rw [mem he] at ha
      exact False.elim ha
    · intro e he
      rw [mem he]
      exact Or.inl (rootEvent_matches _ _ _)
  | node b i j left right ih₁ ih₂ =>
    apply table_node (Nat.le_of_lt_succ b.isLt) (ih₁ l i) (ih₂ (l + b.val + 1) j)
    · intro e he
      have := left.event_bounds l i he
      omega
    · intro e he
      have := right.event_bounds (l + b.val + 1) j he
      omega

end ParseGrammar.OrderedParse

end VPVNP
end Computability
end OAI
