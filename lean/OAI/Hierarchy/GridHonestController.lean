import OAI.Hierarchy.GridSelector
import OAI.Hierarchy.UniversalGrid

namespace OAI
/-! # Reading one grid selector against its fixed evaluator description -/

noncomputable section
namespace Hierarchy.GridThrough
open ThreeFlat.Diagonal.HistoryContraction UniversalGrid
open scoped Classical
variable {F : Type} [Field F] {S : Shape} {a cap : ℕ}

/-- The finite controller on the chosen self-description reads exactly the
native compressed history and uses its actual surviving edge-bit vector. -/
def honestController {T : Type*} (P : Plan F S) (C : P.Codes) (bits : P.History→ℕ)
    (setting : Option (GridSelector.Trace P bits) → T) (chosen : Bits a)
    (input : Bits a) (sel : Bits (cap+1)) : Option T :=
  if input=chosen then (GridSelector.decode P C bits cap sel).map setting else none

end Hierarchy.GridThrough
end

end OAI
