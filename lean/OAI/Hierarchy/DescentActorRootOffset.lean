import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Shape-major physical pointer for a host-major sparse actor number -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window

/-- The printed source is shape-major, while the physical sparse ordinal
is the previous host followed by its local shape. -/
def rootOffset (hosts shapes chunks : ℕ) (i : Fin (hosts*shapes)) :=
  let q:=finProdFinEquiv.symm i
  (q.2.val*hosts+q.1.val)*chunks

def rootLiteral (hosts shapes chunks j : ℕ) :=
  if h:j<hosts*shapes then rootOffset hosts shapes chunks ⟨j,h⟩ else 0

end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
