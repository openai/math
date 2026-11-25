import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # Earlier installed parents from physical grain addresses -/
namespace Hierarchy.DescentOrderedGrainPrecedence
open ProtocolRAMPortRanks
variable {E : Type*} [Fintype E] (width : E→ℕ) (rank : E↪ℕ)

/-- Compare a genuine grain against the start of another genuine parent.
Neither a gap in sparse parent labels nor a zero-width intermediate parent
changes the comparison. -/
theorem before (a b : E) (j : Nat) (inside : j<width a) (start : 0<width b) :
    «prefix» width rank a+j<«prefix» width rank b ↔ rank a<rank b := by
  rcases lt_trichotomy (rank a) (rank b) with old|equal|later
  · have disjoint:=prefix_disjoint width rank old
    exact iff_of_true (by omega) old
  · have same:=rank.injective equal
    subst a
    simp
  · have disjoint:=prefix_disjoint width rank later
    exact iff_of_false (by omega) later.not_gt

theorem first (a b : E) (left : 0<width a) (right : 0<width b) :
    «prefix» width rank a<«prefix» width rank b ↔ rank a<rank b := by
  simpa only [Nat.add_zero] using before width rank a b 0 left right

end Hierarchy.DescentOrderedGrainPrecedence

end OAI
