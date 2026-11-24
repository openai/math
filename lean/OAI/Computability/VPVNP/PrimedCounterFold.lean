import OAI.Computability.VPVNP.PrimedCounterFoldBounds
import OAI.Computability.VPVNP.PrimedCounterChronologySlots
import OAI.Computability.VPVNP.PrimedCounterSiteLoop

/-!
# One logical transition per scheduled parser call

The root initialization overwrites the pending stack. Each of the preceding
calls erases one mark. Comparison looks up the grammar label corresponding
to its dense histogram address. All administrative calls consume empty tapes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Fold

open Chronology

variable {n m s w A S K T : ℕ}

/-- One call after input assembly, either a parser operation at a site or a comparison of a
dense production count. -/
abbrev PostItem (S m K T : ℕ) := (Fin S × Cursor.LocalItem m K) ⊕ Fin T

/-- Absolute cursor of a post-assembly item in the complete pair schedule. -/
def slot (i : PostItem S m K T) : Fin (Cursor.calls A S m K T) :=
  Cursor.index A S m K T (.inr i)

/-- Calls at a given site in execution order, clearing marks, installing its root and then
visiting its nodes. -/
def rowItems (u : Fin S) : List (PostItem S m K T) :=
  (List.finRange m).map (fun j => .inl (u, .inl j)) ++
    [.inl (u, .inr (.inl 0))] ++ (List.finRange K).map (fun j => .inl (u, .inr (.inr j)))

/-- Chronological list of every site's parser calls followed by all production-count
comparisons. -/
def items (S m K T : ℕ) : List (PostItem S m K T) :=
  (List.finRange S).flatMap rowItems ++ (List.finRange T).map Sum.inr

/-- The current absolute cursor selects a complete local choice tape.
Clear, initialize and compare reject a nonempty tape. -/
noncomputable def call (w : ℕ) (d : Fin n) (root : Fin s) (x : Fin S → Fin m → Bool)
    (e : Label n m (Fin s) ≃ Fin T) (μ : Label n m (Fin s) →₀ ℕ) (raw : Tape A S m K T)
    (st : VisitState n m s) (i : PostItem S m K T) : Option (VisitState n m s) :=
  match i with
  | .inl (_, .inl j) =>
    if raw (slot i) = [] then some { st with marked := st.marked.erase j } else none
  | .inl (_, .inr (.inl _)) =>
    if raw (slot i) = [] then some { st with pending := [(d,root)] } else none
  | .inl (u, .inr (.inr _)) => visit w (x u) st (raw (slot i))
  | .inr j =>
    if raw (slot i) = [] ∧ st.counts (e.symm j) = μ (e.symm j) then some st else none

end PrimedCounter.Fold

end VPVNP
end Computability
end OAI
