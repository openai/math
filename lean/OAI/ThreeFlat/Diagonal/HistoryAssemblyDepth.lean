import OAI.ThreeFlat.Diagonal.HistoryStageCharges

namespace OAI
/-! # Depth of copies in the complete selected history -/

namespace ThreeFlat.Diagonal.HistoryContraction

variable {F Pins : Type*} [CommSemiring F] {S : Shape}

namespace Tree

omit [CommSemiring F] in
theorem Within.up {p k : ℕ} {T : Tree F p} (closed : Within k T) : Within (k+1) T := by
  induction closed with
  | atom => exact .atom ..
  | join hs ih => exact .join ih

omit [CommSemiring F] in
theorem Within.mono {p a b : ℕ} {T : Tree F p} (closed : Within a T) (le : a≤b) : Within b T := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le le
  clear le
  induction k with
  | zero => simpa using closed
  | succ k ih => exact ih.up

end Tree

namespace Stage

variable {R : Rewrite S F} {t : Fin R.count} {V : Form S Pins} {W : Form (R.target t) Pins}

theorem within_assemble (A : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) (k : ℕ)
    (old : ∀ u, Tree.Within k (N u)) (kernel : Tree.Within k (A.root v)) :
    Tree.Within (k+1) (A.assemble N v) := by
  apply Tree.Within.join
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact kernel
  · exact old _

end Stage

namespace Plan

def stageCount : {S : Shape} → (P : Plan F S) → P.History → ℕ
  | _, .done _, _ => 0
  | _, .step _ next, h => 1+(next h.1).stageCount h.2

def kernelsWithin (k : ℕ) : {S : Shape} → (P : Plan F S) → (h : P.History) → {V : Form S Pins} → P.Assembly V → Prop
  | _, .done _, _, _, _ => True
  | _, .step _ next, h, _, A => (∀ v, Tree.Within k ((A h.1).2.1.root v)) ∧ kernelsWithin k (next h.1) h.2 (A h.1).2.2

/-- The number of actual chronological rewrites is the only possibly
unbounded contribution to the depth of a compiled terminal history. -/
theorem within_finish (P : Plan F S) (h : P.History) {V : Form S Pins} (A : P.Assembly V)
    (N : Forest F V) (k start : ℕ) (kernel : kernelsWithin k P h A) (le : k≤ start)
    (initial : ∀ v, Tree.Within start (N v)) :
    ∀ v, Tree.Within (start+P.stageCount h) ((P.assemble h A N).2 v) := by
  induction P generalizing start with
  | done => intro v; simpa [assemble,stageCount] using initial v
  | step R next ih =>
    obtain ⟨t,h⟩ := h
    obtain ⟨localBound,remaining⟩ := kernel
    have now v := Stage.within_assemble (A t).2.1 N v start initial ((localBound v).mono le)
    have all := ih t h (A t).2.2 ((A t).2.1.assemble N) (start+1) remaining (by omega) now
    intro v
    simpa [assemble,stageCount,Nat.add_assoc] using all v

end Plan
end ThreeFlat.Diagonal.HistoryContraction

end OAI
