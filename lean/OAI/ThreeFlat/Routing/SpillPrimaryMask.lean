import OAI.ThreeFlat.Routing.SpillLinks

namespace OAI
namespace ThreeFlat.Routing.Spill

variable {L R : Type*} [DecidableEq R]

/-- The unmatched mask consists of the active rows with all primary bits clear. -/
def missedPrimary (A : Finset L) (N : L → Finset R) (h : Candidate N → Bool) : Finset L :=
  A.filter fun i => ∀ r : N i, h ⟨i,r⟩ = false

end ThreeFlat.Routing.Spill

end OAI
