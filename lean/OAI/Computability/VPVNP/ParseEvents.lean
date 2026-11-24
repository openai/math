import OAI.Computability.VPVNP.OrderedParse
import OAI.Computability.VPVNP.ParseIncidenceDefs

/-! # Canonical interval tables of ordered parses -/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar.OrderedParse

variable {V H : Type*} {d : ℕ}

/-- The occurrence at the root interval, including its production choice. -/
def rootEvent : {d : ℕ} → OrderedParse V H d → ℕ → H → ParseEvent V H
  | _, .leaf v, l, h => ⟨l, 0, h, .inl v⟩
  | _ + 1, .node (d := d) b i j _ _, l, h => ⟨l, d + 1, h, .inr (b.val, i, j)⟩

@[simp] theorem rootEvent_matches (t : OrderedParse V H d) (l : ℕ) (h : H) :
    (t.rootEvent l h).Matches l d h := by cases t <;> exact ⟨rfl, rfl, rfl⟩

open scoped Classical

/-- Include the root and concatenate the two children in their leaf intervals. -/
noncomputable def events : {d : ℕ} → OrderedParse V H d → ℕ → H → Finset (ParseEvent V H)
  | _, .leaf v, l, h => {(.leaf v : OrderedParse V H 0).rootEvent l h}
  | _, .node b i j left right, l, h =>
    insert ((.node b i j left right : OrderedParse V H _).rootEvent l h)
      (left.events l i ∪ right.events (l + b.val + 1) j)

@[simp] theorem rootEvent_mem (t : OrderedParse V H d) (l : ℕ) (h : H) :
    t.rootEvent l h ∈ t.events l h := by cases t <;> simp [events]

/-- Every occupied interval is contained in the leaf interval of its ancestor. -/
theorem event_bounds (t : OrderedParse V H d) (l : ℕ) (h : H) {e : ParseEvent V H}
    (he : e ∈ t.events l h) : l ≤ e.start ∧ e.start + e.layer ≤ l + d := by
  induction t generalizing l h with
  | leaf v =>
    simp only [events, Finset.mem_singleton] at he
    subst e
    simp [rootEvent]
  | node b i j left right ih₁ ih₂ =>
    simp only [events, Finset.mem_insert, Finset.mem_union] at he
    rcases he with rfl | h₁ | h₂
    · simp [rootEvent]
    · have := ih₁ l i h₁
      have := b.isLt
      omega
    · have := ih₂ (l + b.val + 1) j h₂
      have := b.isLt
      omega

/-- The left and right subtrees have disjoint occurrences. -/
theorem disjoint_childEvents {k : ℕ} (b : Fin (k + 1)) (i j : H)
    (left : OrderedParse V H b.val) (right : OrderedParse V H (k - b.val)) (l : ℕ) :
    Disjoint (left.events l i) (right.events (l + b.val + 1) j) := by
  rw [Finset.disjoint_left]
  intro e h₁ h₂
  have := left.event_bounds l i h₁
  have := right.event_bounds (l + b.val + 1) j h₂
  omega

theorem rootEvent_notMem_children {k : ℕ} (b : Fin (k + 1)) (i j : H)
    (left : OrderedParse V H b.val) (right : OrderedParse V H (k - b.val)) (l : ℕ) (h : H) :
    (.node b i j left right : OrderedParse V H _).rootEvent l h ∉
      left.events l i ∪ right.events (l + b.val + 1) j := by
  intro he
  rcases Finset.mem_union.mp he with he | he
  · have := left.event_bounds l i he
    simp only [rootEvent] at this
    have := b.isLt
    omega
  · have := right.event_bounds (l + b.val + 1) j he
    simp only [rootEvent] at this
    omega

end ParseGrammar.OrderedParse

end VPVNP
end Computability
end OAI
